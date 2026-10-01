//! Folding casts of literals into literals.

use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::{policy::*, expr::*};

verus! {

impl PrimType {
    /// Returns a literal that every well-formed type reads as `c` converted to this type.
    fn trunc_lit(self, c: i64) -> (res: i64)
        requires self is I || self is U, self.wf()
        ensures forall |arch: Arch, ty: PrimType| ty.wf() ==>
            #[trigger] ty.trunc(arch, res as int) == ty.trunc(arch, self.trunc(arch, c as int))
    {
        let p = self.lit_pattern(Arch::X86_64, c);
        let res = if p <= i64::MAX as u64 { p as i64 } else { -((u64::MAX - p) as i64) - 1 };
        proof {
            if p <= i64::MAX as u64 {
                vstd::arithmetic::div_mod::lemma_small_mod(p as nat, 0x1_0000_0000_0000_0000);
            } else {
                assert(res as int + 0x1_0000_0000_0000_0000 == p as int);
                vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(res as int, 0x1_0000_0000_0000_0000);
                vstd::arithmetic::div_mod::lemma_small_mod(p as nat, 0x1_0000_0000_0000_0000);
            }
            assert(Expr::pat(res as int) == p);
            assert forall |arch: Arch, ty: PrimType| ty.wf() implies
                #[trigger] ty.trunc(arch, res as int) == ty.trunc(arch, self.trunc(arch, c as int)) by {
                assert(self.mask(arch) == self.mask(Arch::X86_64));
                assert(self.trunc(arch, c as int) == self.trunc(Arch::X86_64, c as int));
                ty.lemma_to_bits(arch, res as int);
                ty.lemma_to_bits(arch, self.trunc(arch, c as int));
            }
        }
        res
    }
}

impl Expr {
    /// A cast of `e` has every type a cast of `other` to the same type has, if `e` has every type of `other`.
    proof fn lemma_cast_type(e: Expr, other: Expr, to: PrimType, arch: Arch, ctx: Seq<PrimType>, ty: PrimType)
        requires forall |t: PrimType| #[trigger] other.of_type(arch, ctx, t) ==> e.of_type(arch, ctx, t)
        ensures
            Expr::Cast(Arc::new(other), to).of_type(arch, ctx, ty) ==> Expr::Cast(Arc::new(e), to).of_type(arch, ctx, ty)
    {
        let cast = Expr::Cast(Arc::new(other), to);
        if cast.of_type(arch, ctx, ty) {
            assert(cast.typed(arch, ctx));
            cast.lemma_operands_typed(arch, ctx);
            let t = choose |t: PrimType| other.of_type(arch, ctx, t);
            assert(e.of_type(arch, ctx, t));
            assert(!Expr::BinOp(BinOp::Add, Arc::new(e), Arc::new(e)).of_type(arch, ctx, PrimType::Ptr));
            assert(t.subtype_of(arch, t));
        }
    }

    /// A binary operation on `l` and `r` has every type one on `ol` and `or` has, if `l` and `r`
    /// have every type of `ol` and `or`.
    proof fn lemma_binop_type(op: BinOp, l: Expr, r: Expr, ol: Expr, or: Expr, arch: Arch, ctx: Seq<PrimType>,
        ty: PrimType)
        requires
            forall |t: PrimType| #[trigger] ol.of_type(arch, ctx, t) ==> l.of_type(arch, ctx, t),
            forall |t: PrimType| #[trigger] or.of_type(arch, ctx, t) ==> r.of_type(arch, ctx, t),
        ensures
            Expr::BinOp(op, Arc::new(ol), Arc::new(or)).of_type(arch, ctx, ty)
                ==> Expr::BinOp(op, Arc::new(l), Arc::new(r)).of_type(arch, ctx, ty)
    {
        let other = Expr::BinOp(op, Arc::new(ol), Arc::new(or));
        if other.of_type(arch, ctx, ty) {
            assert(ty != PrimType::Ptr);
            if op is Add || op is Sub {
                let (t1, t2) = other.lemma_operands(arch, ctx, ty);
                assert(l.of_type(arch, ctx, t1));
                assert(r.of_type(arch, ctx, t2));
                assert(t1.subtype_of(arch, t2) || t2.subtype_of(arch, t1));
            } else {
                assert(ol.of_type(arch, ctx, ty));
                assert(or.of_type(arch, ctx, ty));
                assert(l.of_type(arch, ctx, ty));
                assert(r.of_type(arch, ctx, ty));
                assert(ty.subtype_of(arch, ty));
            }
        }
    }

    /// A typed binary operation evaluates like another one with its operator, its types, and
    /// operands that evaluate alike.
    proof fn lemma_binop_eval(self, other: Expr, arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>)
        requires
            self is BinOp,
            other is BinOp,
            self->BinOp_0 == other->BinOp_0,
            self.typed(arch, ctx),
            forall |t: PrimType| #[trigger] other.of_type(arch, ctx, t) == self.of_type(arch, ctx, t),
            other->BinOp_1.eval(arch, ctx, vars) == self->BinOp_1.eval(arch, ctx, vars),
            other->BinOp_2.eval(arch, ctx, vars) == self->BinOp_2.eval(arch, ctx, vars),
        ensures other.eval(arch, ctx, vars) == self.eval(arch, ctx, vars)
    {
        let t = choose |t: PrimType| self.of_type(arch, ctx, t);
        assert(other.of_type(arch, ctx, t));
        assert forall |t1: PrimType, t2: PrimType|
            #[trigger] self.of_type(arch, ctx, t1) && #[trigger] self.of_type(arch, ctx, t2) implies
            t1.bits(arch) == t2.bits(arch) && t1.signed() == t2.signed() by {
            self.lemma_type_unique(arch, ctx, t1, t2);
        }
    }

    /// Returns this expression with each cast of a fixed-width literal folded into a literal.
    pub(super) fn fold(&self) -> (res: Expr)
        ensures
            forall |arch: Arch, ctx: Seq<PrimType>, ty: PrimType|
                #[trigger] res.of_type(arch, ctx, ty) == self.of_type(arch, ctx, ty),
            forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>|
                (exists |ty: PrimType| self.of_type(arch, ctx, ty)) ==>
                #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars),
        decreases self
    {
        match self {
            Expr::Var(i) => Expr::Var(*i),
            Expr::Lit(c, ty) => Expr::Lit(*c, *ty),
            Expr::Cast(e, ty) => {
                let folded = e.fold();
                let ghost inner = folded;
                match folded {
                    Expr::Lit(c, from) if matches!(from, PrimType::I(_) | PrimType::U(_)) && from.exec_wf() => {
                        let res = Expr::Lit(from.trunc_lit(c), *ty);
                        proof {
                            assert forall |arch: Arch, ctx: Seq<PrimType>, t: PrimType|
                                #[trigger] res.of_type(arch, ctx, t) == self.of_type(arch, ctx, t) by {
                                assert(inner.of_type(arch, ctx, from));
                                assert(e.of_type(arch, ctx, from));
                                assert(!Expr::BinOp(BinOp::Add, *e, *e).of_type(arch, ctx, PrimType::Ptr));
                                assert(from.subtype_of(arch, from));
                                if res.of_type(arch, ctx, t) {
                                    assert(t == *ty && t.wf());
                                    assert(self.of_type(arch, ctx, t));
                                }
                            }
                            assert forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>|
                                (exists |t: PrimType| self.of_type(arch, ctx, t)) implies
                                #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars) by {
                                let t = choose |t: PrimType| self.of_type(arch, ctx, t);
                                assert(ty.wf());
                                assert(inner.of_type(arch, ctx, from));
                                assert(e.of_type(arch, ctx, from));
                                assert(inner.eval(arch, ctx, vars) == e.eval(arch, ctx, vars));
                            }
                        }
                        res
                    }
                    folded => {
                        let res = Expr::Cast(Arc::new(folded), *ty);
                        proof {
                            assert forall |arch: Arch, ctx: Seq<PrimType>, t: PrimType|
                                #[trigger] res.of_type(arch, ctx, t) == self.of_type(arch, ctx, t) by {
                                Self::lemma_cast_type(**e, inner, *ty, arch, ctx, t);
                                Self::lemma_cast_type(inner, **e, *ty, arch, ctx, t);
                            }
                            assert forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>|
                                (exists |t: PrimType| self.of_type(arch, ctx, t)) implies
                                #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars) by {
                                assert(self.typed(arch, ctx));
                                self.lemma_operands_typed(arch, ctx);
                                assert(inner.eval(arch, ctx, vars) == e.eval(arch, ctx, vars));
                            }
                        }
                        res
                    }
                }
            }
            Expr::BinOp(op, l, r) => {
                let folded_l = l.fold();
                let folded_r = r.fold();
                let ghost (gl, gr) = (folded_l, folded_r);
                let res = Expr::BinOp(*op, Arc::new(folded_l), Arc::new(folded_r));
                proof {
                    assert forall |arch: Arch, ctx: Seq<PrimType>, t: PrimType|
                        #[trigger] res.of_type(arch, ctx, t) == self.of_type(arch, ctx, t) by {
                        Self::lemma_binop_type(*op, **l, **r, gl, gr, arch, ctx, t);
                        Self::lemma_binop_type(*op, gl, gr, **l, **r, arch, ctx, t);
                    }
                    assert forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>|
                        (exists |t: PrimType| self.of_type(arch, ctx, t)) implies
                        #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars) by {
                        assert(self.typed(arch, ctx));
                        self.lemma_operands_typed(arch, ctx);
                        assert(gl.eval(arch, ctx, vars) == l.eval(arch, ctx, vars));
                        assert(gr.eval(arch, ctx, vars) == r.eval(arch, ctx, vars));
                        self.lemma_binop_eval(res, arch, ctx, vars);
                    }
                }
                res
            }
        }
    }
}

impl Cond {
    /// Returns this condition with the casts in its comparisons folded.
    pub(super) fn fold(&self) -> (res: Cond)
        ensures
            *self == Cond::True ==> res == Cond::True,
            forall |arch: Arch, ctx: Seq<PrimType>| #[trigger] res.wf(arch, ctx) == self.wf(arch, ctx),
            forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>| self.wf(arch, ctx) ==>
                #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars),
        decreases self
    {
        match self {
            Cond::True => Cond::True,
            Cond::False => Cond::False,
            Cond::Cmp(op, l, r) => {
                let folded_l = l.fold();
                let folded_r = r.fold();
                let ghost (gl, gr) = (folded_l, folded_r);
                let res = Cond::Cmp(*op, Arc::new(folded_l), Arc::new(folded_r));
                proof {
                    assert forall |arch: Arch, ctx: Seq<PrimType>| #[trigger] res.wf(arch, ctx) == self.wf(arch, ctx) by {
                        if self.wf(arch, ctx) {
                            let (t1, t2) = choose |t1: PrimType, t2: PrimType| {
                                &&& l.of_type(arch, ctx, t1)
                                &&& r.of_type(arch, ctx, t2)
                                &&& t1 == PrimType::Ptr ==> *op == CmpOp::Eq
                                &&& t2 == PrimType::Ptr ==> *op == CmpOp::Eq
                                &&& t1.subtype_of(arch, t2) || t2.subtype_of(arch, t1)
                            };
                            assert(gl.of_type(arch, ctx, t1) && gr.of_type(arch, ctx, t2));
                        }
                        if res.wf(arch, ctx) {
                            let (t1, t2) = choose |t1: PrimType, t2: PrimType| {
                                &&& gl.of_type(arch, ctx, t1)
                                &&& gr.of_type(arch, ctx, t2)
                                &&& t1 == PrimType::Ptr ==> *op == CmpOp::Eq
                                &&& t2 == PrimType::Ptr ==> *op == CmpOp::Eq
                                &&& t1.subtype_of(arch, t2) || t2.subtype_of(arch, t1)
                            };
                            assert(l.of_type(arch, ctx, t1) && r.of_type(arch, ctx, t2));
                        }
                    }
                    assert forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>| self.wf(arch, ctx) implies
                        #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars) by {
                        let (t1, t2) = choose |t1: PrimType, t2: PrimType| {
                            &&& l.of_type(arch, ctx, t1)
                            &&& r.of_type(arch, ctx, t2)
                            &&& t1 == PrimType::Ptr ==> *op == CmpOp::Eq
                            &&& t2 == PrimType::Ptr ==> *op == CmpOp::Eq
                            &&& t1.subtype_of(arch, t2) || t2.subtype_of(arch, t1)
                        };
                        assert(gl.eval(arch, ctx, vars) == l.eval(arch, ctx, vars));
                        assert(gr.eval(arch, ctx, vars) == r.eval(arch, ctx, vars));
                    }
                }
                res
            }
            Cond::And(l, r) => {
                let folded_l = l.fold();
                let folded_r = r.fold();
                let ghost (gl, gr) = (folded_l, folded_r);
                let res = Cond::And(Arc::new(folded_l), Arc::new(folded_r));
                proof {
                    assert forall |arch: Arch, ctx: Seq<PrimType>| #[trigger] res.wf(arch, ctx) == self.wf(arch, ctx) by {
                        assert(gl.wf(arch, ctx) == l.wf(arch, ctx));
                        assert(gr.wf(arch, ctx) == r.wf(arch, ctx));
                    }
                    assert forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>| self.wf(arch, ctx) implies
                        #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars) by {
                        assert(gl.eval(arch, ctx, vars) == l.eval(arch, ctx, vars));
                        assert(gr.eval(arch, ctx, vars) == r.eval(arch, ctx, vars));
                    }
                }
                res
            }
            Cond::Or(l, r) => {
                let folded_l = l.fold();
                let folded_r = r.fold();
                let ghost (gl, gr) = (folded_l, folded_r);
                let res = Cond::Or(Arc::new(folded_l), Arc::new(folded_r));
                proof {
                    assert forall |arch: Arch, ctx: Seq<PrimType>| #[trigger] res.wf(arch, ctx) == self.wf(arch, ctx) by {
                        assert(gl.wf(arch, ctx) == l.wf(arch, ctx));
                        assert(gr.wf(arch, ctx) == r.wf(arch, ctx));
                    }
                    assert forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>| self.wf(arch, ctx) implies
                        #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars) by {
                        assert(gl.eval(arch, ctx, vars) == l.eval(arch, ctx, vars));
                        assert(gr.eval(arch, ctx, vars) == r.eval(arch, ctx, vars));
                    }
                }
                res
            }
            Cond::Not(c) => {
                let folded = c.fold();
                let ghost g = folded;
                let res = Cond::Not(Arc::new(folded));
                proof {
                    assert forall |arch: Arch, ctx: Seq<PrimType>| #[trigger] res.wf(arch, ctx) == self.wf(arch, ctx) by {
                        assert(g.wf(arch, ctx) == c.wf(arch, ctx));
                    }
                    assert forall |arch: Arch, ctx: Seq<PrimType>, vars: Seq<u64>| self.wf(arch, ctx) implies
                        #[trigger] res.eval(arch, ctx, vars) == self.eval(arch, ctx, vars) by {
                        assert(g.eval(arch, ctx, vars) == c.eval(arch, ctx, vars));
                    }
                }
                res
            }
        }
    }
}

} // verus!
