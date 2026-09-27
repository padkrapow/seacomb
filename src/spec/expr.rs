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
pub enum CmpOp { Eq, Lt, Le }

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum ArithOp { Add, Sub, Mul }

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum BitwiseOp { And, Or, Xor }

/// A simple expression language to describe rule constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// A free variable.
    Var(u32),
    /// A literal bitcasted to the expected type.
    Lit(i64, PrimType),
    /// Explicit casting.
    Cast(Arc<Expr>, PrimType),
    /// Comparison ops.
    Cmp(CmpOp, Arc<Expr>, Arc<Expr>),
    /// Arithmetic ops.
    Arith(ArithOp, Arc<Expr>, Arc<Expr>),
    /// Nitwise ops.
    Bitwise(BitwiseOp, Arc<Expr>, Arc<Expr>),
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
}

impl Expr {
    /// Whether the expression can have the given type.
    pub open spec fn of_type(self, arch: Arch, ctx: Seq<PrimType>, ty: PrimType) -> bool
        decreases self
    {
        match self {
            Expr::Var(i) => i < ctx.len() && ty == ctx[i as int],
            Expr::Lit(c, cty) => ty == cty,
            Expr::Cast(e, cty) => ty == cty && exists |ety: PrimType| e.of_type(arch, ctx, ety),
            Expr::Cmp(op, e1, e2) => exists |ty1: PrimType, ty2: PrimType| {
                &&& e1.of_type(arch, ctx, ty1)
                &&& e2.of_type(arch, ctx, ty2)
                &&& ty1 == PrimType::Ptr ==> op == CmpOp::Eq
                &&& ty2 == PrimType::Ptr ==> op == CmpOp::Eq
                // Implicit casting
                &&& ty1.subtype_of(arch, ty2) || ty2.subtype_of(arch, ty1)
                &&& ty == PrimType::U(1)
            },
            Expr::Arith(op, e1, e2) => exists |ty1: PrimType, ty2: PrimType| {
                &&& e1.of_type(arch, ctx, ty1)
                &&& e2.of_type(arch, ctx, ty2)
                &&& ty1 != PrimType::Ptr
                &&& ty2 != PrimType::Ptr
                &&& {
                    // Implicit casting, and the result is the "larger" type.
                    ||| ty1.subtype_of(arch, ty2) && ty == ty2
                    ||| ty2.subtype_of(arch, ty1) && ty == ty1
                }
            },
            Expr::Bitwise(op, e1, e2) => exists |ety: PrimType| {
                // No implicit casting in bitwise ops.
                &&& e1.of_type(arch, ctx, ety)
                &&& e2.of_type(arch, ctx, ety)
                &&& ety != PrimType::Ptr
                &&& ty == ety
            },
        }
    }
}

} // verus!

// Semantics
verus! {

impl Expr {
    /// Denotes the expression as an integer in the range of its type.
    pub open spec fn eval(self, arch: Arch, ctx: Seq<PrimType>, args: Seq<u64>) -> int
        decreases self
    {
        match self {
            Expr::Var(i) => ctx[i as int].to_int(arch, args[i as int]),
            Expr::Lit(c, cty) => cty.trunc(arch, c as int),
            Expr::Cast(e, cty) => cty.trunc(arch, e.eval(arch, ctx, args)),
            Expr::Cmp(op, e1, e2) => {
                let v1 = e1.eval(arch, ctx, args);
                let v2 = e2.eval(arch, ctx, args);
                let holds = match op {
                    CmpOp::Eq => v1 == v2,
                    CmpOp::Lt => v1 < v2,
                    CmpOp::Le => v1 <= v2,
                };
                if holds { 1 } else { 0 }
            }
            // Wraps around at the result type.
            Expr::Arith(op, e1, e2) => {
                let ty = choose |ty: PrimType| self.of_type(arch, ctx, ty);
                let v1 = e1.eval(arch, ctx, args);
                let v2 = e2.eval(arch, ctx, args);
                let v = match op {
                    ArithOp::Add => v1 + v2,
                    ArithOp::Sub => v1 - v2,
                    ArithOp::Mul => v1 * v2,
                };
                ty.trunc(arch, v)
            }
            Expr::Bitwise(op, e1, e2) => {
                let ty = choose |ty: PrimType| self.of_type(arch, ctx, ty);
                let v1 = ty.to_bits(arch, e1.eval(arch, ctx, args));
                let v2 = ty.to_bits(arch, e2.eval(arch, ctx, args));
                let v = match op {
                    BitwiseOp::And => v1 & v2,
                    BitwiseOp::Or => v1 | v2,
                    BitwiseOp::Xor => v1 ^ v2,
                };
                ty.to_int(arch, v)
            }
        }
    }
}

} // verus!
