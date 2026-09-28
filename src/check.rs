//! Policy validation (i.e., executable versions of the `wf` specs).

use vstd::prelude::*;
use crate::spec::{policy::*, expr::*};

verus! {

/// An error while validating a filter policy.
#[verifier::external_derive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
#[allow(inconsistent_fields)]
pub enum CheckError {
    /// Invalid errno number.
    #[error("invalid errno number {0}")]
    InvalidErrno(u16),
    /// An argument index past the end of a syscall signature.
    #[error("argument {given} is out of range ({total} arguments)")]
    InvalidArg { given: u32, total: u32 },
    /// A type of an unsupported width.
    #[error("{0:?} is not a supported width")]
    InvalidWidth(PrimType),
    /// A comparison has operands that are ordered pointers or that neither convert to the other.
    #[error("{op} cannot be applied to {lhs} and {rhs}")]
    CmpTypes { op: CmpOp, lhs: PrimType, rhs: PrimType },
    /// A binary operation has a pointer operand, or operands it cannot combine.
    #[error("{op} cannot be applied to {lhs} and {rhs}")]
    BinOpTypes { op: BinOp, lhs: PrimType, rhs: PrimType },
    /// A rule has conditions on a syscall whose signatures differ across architectures.
    #[error("syscall signatures differ across enabled architectures")]
    IncompatSigs,
    /// A multiplexed syscall rule cannot have argument conditions.
    #[error("multiplexed syscall rule cannot have argument conditions; use add_rule_exact")]
    InvalidMuxConditions,
    /// The filter already includes this architecture.
    #[error("filter already includes this architecture")]
    DuplicateArch,
}

impl Action {
    /// Checks whether this action contains a valid value.
    pub(crate) fn check(&self) -> (res: Result<(), CheckError>)
        ensures res is Ok <==> self.wf()
    {
        match self {
            Action::Errno(e) if (*e as u32) > Self::MAX_ERRNO => Err(CheckError::InvalidErrno(*e)),
            _ => Ok(()),
        }
    }
}

impl PrimType {
    /// Executable version of [`PrimType::subtype_of`].
    pub(crate) fn exec_subtype_of(self, arch: Arch, other: PrimType) -> (res: bool)
        ensures res == self.subtype_of(arch, other)
    {
        if self == PrimType::Ptr || other == PrimType::Ptr {
            self == PrimType::Ptr && other == PrimType::Ptr
        } else {
            let bits = self.exec_bits(arch);
            let other_bits = other.exec_bits(arch);
            self.exec_signed() == other.exec_signed() && bits <= other_bits
                || !self.exec_signed() && other.exec_signed() && bits < other_bits
        }
    }

    /// Checks that this type has a supported width.
    fn check(self) -> (res: Result<(), CheckError>)
        ensures res is Ok <==> self.wf()
    {
        if self.exec_wf() { Ok(()) } else { Err(CheckError::InvalidWidth(self)) }
    }
}

impl Expr {
    /// Returns a type of this expression over a signature `sig` on `arch`, and whether it
    /// also has every type that converts to and from that one.
    pub(crate) fn check(&self, arch: Arch, sig: &[PrimType]) -> (res: Result<(PrimType, bool), CheckError>)
        ensures
            res matches Ok((ty, _)) ==> self.of_type(arch, sig@, ty),
            res matches Ok((ty, true)) ==> forall |t: PrimType|
                t.subtype_of(arch, ty) && ty.subtype_of(arch, t) ==> #[trigger] self.of_type(arch, sig@, t),
        decreases self
    {
        match self {
            Expr::Var(i) => {
                if *i as usize >= sig.len() {
                    return Err(CheckError::InvalidArg { given: *i, total: sig.len() as u32 });
                }
                sig[*i as usize].check()?;
                Ok((sig[*i as usize], false))
            }
            Expr::Lit(_, ty) => {
                ty.check()?;
                Ok((*ty, false))
            }
            Expr::Cast(e, ty) => {
                #[allow(unused_variables)]
                let (from, _) = e.check(arch, sig)?;
                ty.check()?;
                proof {
                    // Denying the sum a pointer type brings up the operand at the fuel
                    // `of_type` looks for it at.
                    assert(!Expr::BinOp(BinOp::Add, *e, *e).of_type(arch, sig@, PrimType::Ptr));
                    assert(from.subtype_of(arch, from));
                }
                Ok((*ty, false))
            }
            Expr::BinOp(op, l, r) => {
                let (t1, all1) = l.check(arch, sig)?;
                let (t2, all2) = r.check(arch, sig)?;
                let up = t1.exec_subtype_of(arch, t2);
                let down = t2.exec_subtype_of(arch, t1);
                let err = CheckError::BinOpTypes { op: *op, lhs: t1, rhs: t2 };
                if t1 == PrimType::Ptr || t2 == PrimType::Ptr || !up && !down {
                    return Err(err);
                }
                match op {
                    BinOp::Add | BinOp::Sub => {
                        // The result takes the larger type, or either one if each converts to the other.
                        let (ty, all) = if !down {
                            (t2, all2)
                        } else if !up {
                            (t1, all1)
                        } else {
                            (t1, all1 || all2 || t1 != t2)
                        };
                        proof {
                            assert forall |t: PrimType| all && t.subtype_of(arch, ty) && ty.subtype_of(arch, t)
                                implies #[trigger] self.of_type(arch, sig@, t) by {
                                if all1 && ty == t1 {
                                    assert(l.of_type(arch, sig@, t));
                                    assert(t2.subtype_of(arch, t));
                                } else if all2 {
                                    assert(r.of_type(arch, sig@, t));
                                    assert(t1.subtype_of(arch, t));
                                } else {
                                    // Two distinct types that each convert to the other are the
                                    // only types that do so with either.
                                    assert(t == t1 || t == t2);
                                }
                            }
                        }
                        Ok((ty, all))
                    }
                    _ => {
                        // No implicit casting, but an operand may also have types besides the one returned.
                        if !up || !down || t1 != t2 && !all1 && !all2 {
                            return Err(err);
                        }
                        let ty = if all1 { t2 } else { t1 };
                        proof {
                            assert forall |t: PrimType| t == ty || all1 && all2 && t.subtype_of(arch, ty)
                                && ty.subtype_of(arch, t) implies #[trigger] self.of_type(arch, sig@, t) by {
                                assert(l.of_type(arch, sig@, t));
                                assert(r.of_type(arch, sig@, t));
                                assert(t.subtype_of(arch, t));
                            }
                        }
                        Ok((ty, all1 && all2))
                    }
                }
            }
        }
    }
}

impl Cond {
    /// Checks that this condition is well-typed over a signature `sig` on `arch`.
    pub(crate) fn check(&self, arch: Arch, sig: &[PrimType]) -> (res: Result<(), CheckError>)
        ensures res is Ok ==> self.wf(arch, sig@)
        decreases self
    {
        match self {
            Cond::True | Cond::False => Ok(()),
            Cond::Cmp(op, l, r) => {
                let (t1, _) = l.check(arch, sig)?;
                let (t2, _) = r.check(arch, sig)?;
                // Pointers only compare for equality.
                if (t1 == PrimType::Ptr || t2 == PrimType::Ptr) && *op != CmpOp::Eq
                    || !t1.exec_subtype_of(arch, t2) && !t2.exec_subtype_of(arch, t1) {
                    return Err(CheckError::CmpTypes { op: *op, lhs: t1, rhs: t2 });
                }
                Ok(())
            }
            Cond::And(l, r) | Cond::Or(l, r) => {
                l.check(arch, sig)?;
                r.check(arch, sig)
            }
            Cond::Not(c) => c.check(arch, sig),
        }
    }
}

impl Rule {
    /// Checks the rule against every enabled architecture.
    pub(crate) fn check(&self, archs: &[Arch]) -> (res: Result<(), CheckError>)
        ensures res is Ok ==> self.wf(archs@)
    {
        self.action.check()?;
        let cond = &*self.cond;
        let constrained = !matches!(cond, Cond::True);
        if constrained && !self.no_mux && (self.syscall.socketcall_arg().is_some() || self.syscall.ipc_arg().is_some()) {
            return Err(CheckError::InvalidMuxConditions);
        }
        if archs.is_empty() {
            return Ok(());
        }
        let first = self.syscall.signature(archs[0]);
        let mut i: usize = 0;
        while i < archs.len()
            invariant
                0 < archs@.len(),
                cond == *self.cond,
                constrained == (*self.cond != Cond::True),
                first@ =~= self.syscall.spec_signature(archs@[0]),
                i <= archs@.len(),
                constrained ==> forall |k: int| 0 <= k < i ==>
                    self.syscall.spec_signature(#[trigger] archs@[k]) =~= first@,
                forall |k: int| 0 <= k < i ==>
                    cond.wf(#[trigger] archs@[k], self.syscall.spec_signature(archs@[k])),
            decreases archs@.len() - i
        {
            let arch = archs[i];
            let sig = self.syscall.signature(arch);
            if constrained {
                if sig.len() != first.len() {
                    return Err(CheckError::IncompatSigs);
                }
                let mut t: usize = 0;
                while t < sig.len()
                    invariant
                        t <= sig@.len(),
                        sig@.len() == first@.len(),
                        forall |k: int| 0 <= k < t ==> sig@[k] == first@[k],
                    decreases sig@.len() - t
                {
                    if sig[t] != first[t] {
                        return Err(CheckError::IncompatSigs);
                    }
                    t += 1;
                }
                proof {
                    assert(sig@ =~= first@);
                }
            }
            cond.check(arch, sig)?;
            i += 1;
        }
        proof {
            assert forall |k: int, l: int| #![trigger archs@[k], archs@[l]] 0 <= k < l < archs@.len()
                && self.syscall.spec_signature(archs@[k])
                    != self.syscall.spec_signature(archs@[l])
                implies *self.cond == Cond::True by {
                if constrained {
                    assert(self.syscall.spec_signature(archs@[k]) =~= first@);
                    assert(self.syscall.spec_signature(archs@[l]) =~= first@);
                }
            }
        }
        Ok(())
    }
}

} // verus!

impl std::fmt::Display for PrimType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimType::I(n) => write!(f, "i{n}"),
            PrimType::U(n) => write!(f, "u{n}"),
            PrimType::IWord => write!(f, "isize"),
            PrimType::UWord => write!(f, "usize"),
            PrimType::Ptr => write!(f, "ptr"),
        }
    }
}

impl std::fmt::Display for CmpOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            CmpOp::Eq => "Equality",
            CmpOp::Lt => "Less-than",
            CmpOp::Le => "Less-or-equal",
        })
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            BinOp::Add => "Addition",
            BinOp::Sub => "Subtraction",
            BinOp::And => "Bitwise and",
            BinOp::Or => "Bitwise or",
            BinOp::Xor => "Bitwise xor",
        })
    }
}
