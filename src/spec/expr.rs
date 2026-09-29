//! Abstract syntax and semantics of a simple, typed expression language.

use vstd::prelude::*;
use std::sync::Arc;
use super::policy::Arch;

// Syntax
verus! {

/// Primitive types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum PrimType {
    I(u32),
    U(u32),
    IWord,
    UWord,
    Ptr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum BinOp { Add, Sub, And, Or, Xor }

/// Arithmetic expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
// Verus does not yet model non-Copy Clone derives.
#[verifier::external_derive(Clone)]
pub enum Expr {
    /// A free variable.
    Var(u32),
    /// A literal bitcasted to the expected type.
    Lit(i64, PrimType),
    /// Explicit casting.
    Cast(Arc<Expr>, PrimType),
    /// Arithmetic/bitwise binary ops.
    BinOp(BinOp, Arc<Expr>, Arc<Expr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum CmpOp { Eq, Lt, Le }

/// Boolean conditions.
#[derive(Debug, Clone, PartialEq, Eq)]
// Verus does not yet model non-Copy Clone derives.
#[verifier::external_derive(Clone)]
pub enum Cond {
    True, False,
    Cmp(CmpOp, Arc<Expr>, Arc<Expr>),
    And(Arc<Cond>, Arc<Cond>),
    Or(Arc<Cond>, Arc<Cond>),
    Not(Arc<Cond>),
}

impl Arch {
    /// Bitwidth of a machine word on this arch.
    pub open spec fn word_bits(self) -> u64 {
        match self {
            Arch::X86_64 | Arch::Aarch64 => 64,
            Arch::X86 | Arch::Arm => 32,
        }
    }
}

impl PrimType {
    /// Bitwidth of the primitive type on the given arch.
    pub open spec fn bits(self, arch: Arch) -> u64 {
        match self {
            PrimType::I(n) => n as u64,
            PrimType::U(n) => n as u64,
            _ => arch.word_bits(),
        }
    }

    pub open spec fn mask(self, arch: Arch) -> u64 {
        if self.bits(arch) >= 64 { u64::MAX } else { ((1u64 << self.bits(arch)) - 1) as u64 }
    }

    pub open spec fn signed(self) -> bool {
        self is I || self is IWord
    }

    /// Bitcasts `value` to this type, interpreted as an unbounded integer.
    pub open spec fn to_int(self, arch: Arch, value: u64) -> int {
        let pattern = value & self.mask(arch);
        if self.signed() && pattern > self.mask(arch) >> 1u64 {
            pattern - (self.mask(arch) + 1)
        } else {
            pattern as int
        }
    }

    /// Reduces `value` modulo `2^bits` to the bits of this type.
    pub open spec fn to_bits(self, arch: Arch, value: int) -> u64 {
        (value % (self.mask(arch) + 1)) as u64
    }

    /// Converts `value` to this type, as C does.
    pub open spec fn trunc(self, arch: Arch, value: int) -> int {
        self.to_int(arch, self.to_bits(arch, value))
    }

    /// Whether any value of the given type can be (implicitly) casted to
    /// the other type without any loss of data.
    pub open spec fn subtype_of(self, arch: Arch, other: PrimType) -> bool {
        // Pointers must be explicitly casted.
        ||| self == PrimType::Ptr && other == PrimType::Ptr
        ||| self != PrimType::Ptr && other != PrimType::Ptr && {
            ||| self.signed() == other.signed() && self.bits(arch) <= other.bits(arch)
            ||| !self.signed() && other.signed() && self.bits(arch) < other.bits(arch)
        }
    }

    /// Only supporting 8/16/32/64-bit integers
    pub open spec fn wf(self) -> bool {
        match self {
            PrimType::I(n) | PrimType::U(n) => n == 8 || n == 16 || n == 32 || n == 64,
            _ => true,
        }
    }
}

impl Expr {
    /// Whether the expression can have the given type.
    pub open spec fn of_type(self, arch: Arch, ctx: Seq<PrimType>, ty: PrimType) -> bool
        decreases self
    {
        &&& ty.wf()
        &&& match self {
            Expr::Var(i) => i < ctx.len() && ty == ctx[i as int],
            Expr::Lit(c, cty) => ty == cty,
            Expr::Cast(e, cty) => ty == cty && exists |ety: PrimType| e.of_type(arch, ctx, ety),
            Expr::BinOp(op, e1, e2) => exists |ty1: PrimType, ty2: PrimType| {
                &&& e1.of_type(arch, ctx, ty1)
                &&& e2.of_type(arch, ctx, ty2)
                &&& ty1 != PrimType::Ptr
                &&& ty2 != PrimType::Ptr
                &&& match op {
                    // Implicit casting, and the result is the "larger" type.
                    BinOp::Add | BinOp::Sub => {
                        ||| ty1.subtype_of(arch, ty2) && ty == ty2
                        ||| ty2.subtype_of(arch, ty1) && ty == ty1
                    },
                    // No implicit casting in bitwise ops.
                    _ => ty1 == ty2 && ty == ty1,
                }
            },
        }
    }
}

impl Cond {
    /// Whether the condition is well-typed.
    pub open spec fn wf(self, arch: Arch, ctx: Seq<PrimType>) -> bool
        decreases self
    {
        match self {
            Cond::True | Cond::False => true,
            Cond::Cmp(op, e1, e2) => exists |ty1: PrimType, ty2: PrimType| {
                &&& e1.of_type(arch, ctx, ty1)
                &&& e2.of_type(arch, ctx, ty2)
                &&& ty1 == PrimType::Ptr ==> op == CmpOp::Eq
                &&& ty2 == PrimType::Ptr ==> op == CmpOp::Eq
                // Implicit casting
                &&& ty1.subtype_of(arch, ty2) || ty2.subtype_of(arch, ty1)
            },
            Cond::And(c1, c2) => c1.wf(arch, ctx) && c2.wf(arch, ctx),
            Cond::Or(c1, c2) => c1.wf(arch, ctx) && c2.wf(arch, ctx),
            Cond::Not(c) => c.wf(arch, ctx),
        }
    }
}

} // verus!

// Semantics
verus! {

impl Expr {
    /// Denotes the expression as an integer in the range of its type.
    pub open spec fn eval(self, arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>) -> int
        decreases self
    {
        match self {
            Expr::Var(i) => ctx[i as int].to_int(arch, vars[i as int]),
            Expr::Lit(c, cty) => cty.trunc(arch, c as int),
            Expr::Cast(e, cty) => cty.trunc(arch, e.eval(arch, ctx, vars)),
            Expr::BinOp(op, e1, e2) => {
                let ty = choose |ty: PrimType| self.of_type(arch, ctx, ty);
                let v1 = e1.eval(arch, ctx, vars);
                let v2 = e2.eval(arch, ctx, vars);
                match op {
                    BinOp::Add => ty.trunc(arch, v1 + v2),
                    BinOp::Sub => ty.trunc(arch, v1 - v2),
                    BinOp::And => ty.to_int(arch, ty.to_bits(arch, v1) & ty.to_bits(arch, v2)),
                    BinOp::Or => ty.to_int(arch, ty.to_bits(arch, v1) | ty.to_bits(arch, v2)),
                    BinOp::Xor => ty.to_int(arch, ty.to_bits(arch, v1) ^ ty.to_bits(arch, v2)),
                }
            }
        }
    }
}

impl Cond {
    /// Whether the condition holds.
    pub open spec fn eval(self, arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>) -> bool
        decreases self
    {
        match self {
            Cond::True => true,
            Cond::False => false,
            Cond::Cmp(op, e1, e2) => {
                let v1 = e1.eval(arch, ctx, vars);
                let v2 = e2.eval(arch, ctx, vars);
                match op {
                    CmpOp::Eq => v1 == v2,
                    CmpOp::Lt => v1 < v2,
                    CmpOp::Le => v1 <= v2,
                }
            }
            Cond::And(c1, c2) => c1.eval(arch, ctx, vars) && c2.eval(arch, ctx, vars),
            Cond::Or(c1, c2) => c1.eval(arch, ctx, vars) || c2.eval(arch, ctx, vars),
            Cond::Not(c) => !c.eval(arch, ctx, vars),
        }
    }
}

} // verus!
