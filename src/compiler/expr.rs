//! Compiling rule conditions: the jumps that combine them, and the comparisons at their leaves.

use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::{policy::*, expr::*, cbpf::*};
use super::CompileError;
use super::builder::{Builder, Label};
#[allow(unused_imports)]
use super::machine::Regs;

verus! {

impl PrimType {
    /// Returns the width of this type on `arch`.
    pub(crate) fn exec_bits(self, arch: Arch) -> (res: u32)
        ensures res as u64 == self.bits(arch)
    {
        match self {
            PrimType::I(n) | PrimType::U(n) => n,
            _ => if arch == Arch::X86_64 || arch == Arch::Aarch64 { 64 } else { 32 },
        }
    }

    /// Whether this type is signed.
    pub(crate) fn exec_signed(self) -> (res: bool)
        ensures res == self.signed()
    {
        matches!(self, PrimType::I(_) | PrimType::IWord)
    }

    /// Whether this type has a supported width.
    pub(crate) fn exec_wf(self) -> (res: bool)
        ensures res == self.wf()
    {
        match self {
            PrimType::I(n) | PrimType::U(n) => n == 8 || n == 16 || n == 32 || n == 64,
            _ => true,
        }
    }

    /// Returns the mask of this type on `arch`.
    pub(crate) fn exec_mask(self, arch: Arch) -> (res: u64)
        ensures res == self.mask(arch)
    {
        let bits = self.exec_bits(arch);
        if bits >= 64 {
            u64::MAX
        } else {
            proof {
                assert((1u64 << bits) != 0) by (bit_vector)
                    requires bits < 64;
            }
            (1u64 << bits) - 1
        }
    }

    /// Reading a value back into this type's bits gives the bits it was read from.
    proof fn lemma_to_int_bits(self, arch: Arch, x: u64)
        ensures self.to_bits(arch, self.to_int(arch, x)) == x & self.mask(arch)
    {
        let mask = self.mask(arch);
        let pattern = x & mask;
        assert((x & mask) <= mask) by (bit_vector);
        let modulus: int = mask as int + 1;
        vstd::arithmetic::div_mod::lemma_small_mod(pattern as nat, modulus as nat);
        if self.signed() && pattern > mask >> 1u64 {
            vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(pattern as int, modulus);
            assert((pattern as int - modulus) % modulus == pattern as int);
        }
    }

    /// Two words read as the same value exactly when they agree within the mask.
    proof fn lemma_to_int_eq(self, arch: Arch, x: u64, y: u64)
        ensures
            (self.to_int(arch, x) == self.to_int(arch, y))
                <==> (x & self.mask(arch) == y & self.mask(arch)),
    {
        self.lemma_to_int_bits(arch, x);
        self.lemma_to_int_bits(arch, y);
    }

    /// Flipping bit 63 turns signed 64-bit ordering into unsigned ordering.
    proof fn lemma_signed_bias_64(self, arch: Arch, x: u64, y: u64)
        requires self.signed(), self.bits(arch) == 64
        ensures
            (self.to_int(arch, x) < self.to_int(arch, y))
                <==> ((x ^ 0x8000_0000_0000_0000u64)
                    < (y ^ 0x8000_0000_0000_0000u64))
    {
        let mask = self.mask(arch);
        let half = mask >> 1u64;
        let bias = 0x8000_0000_0000_0000u64;
        assert(mask == u64::MAX);
        assert((x & mask) == x) by (bit_vector) requires mask == u64::MAX;
        assert((y & mask) == y) by (bit_vector) requires mask == u64::MAX;
        assert((mask >> 1u64) == 0x7FFF_FFFF_FFFF_FFFF) by (bit_vector)
            requires mask == u64::MAX;
        assert(((x ^ bias) < (y ^ bias)) <==>
            ((x > half && y <= half) || ((x > half) == (y > half) && x < y)))
            by (bit_vector)
            requires half == 0x7FFF_FFFF_FFFF_FFFF,
                bias == 0x8000_0000_0000_0000u64;
        if x > half {
            if y > half {
                assert(self.to_int(arch, x) == x as int - (mask as int + 1));
                assert(self.to_int(arch, y) == y as int - (mask as int + 1));
            }
        } else if y > half {
            assert(self.to_int(arch, x) == x as int);
            assert(self.to_int(arch, y) == y as int - (mask as int + 1));
        }
    }
}

impl CmpOp {
    /// Whether `x` compares to `k` under this operator.
    pub(super) open spec fn holds(self, x: int, k: int) -> bool {
        match self {
            CmpOp::Eq => x == k,
            CmpOp::Lt => x < k,
            CmpOp::Le => x <= k,
        }
    }

    /// Whether the two-word test passes on the high and low words as it loads them.
    pub(super) open spec fn wide_holds(self, high: u32, low: u32, k_hi: u32, k_lo: u32) -> bool {
        if high == k_hi {
            self.holds(low as int, k_lo as int)
        } else {
            !(self is Eq) && high < k_hi
        }
    }

    /// The jump, as [`Builder::emit_jump`] takes it, that a failing one-word test takes.
    fn fail_jump(self) -> (res: (JmpOp, bool))
        ensures forall |x: u32, k: u32| #[trigger] res.0.eval(x, k) == res.1 <==> !self.holds(x as int, k as int)
    {
        match self {
            CmpOp::Eq => (JmpOp::Eq, false),
            CmpOp::Lt => (JmpOp::Ge, true),
            CmpOp::Le => (JmpOp::Gt, true),
        }
    }

    /// A 64-bit value seen as two 32-bit words: comparisons settle on the high word
    /// unless the two are equal, and a mask applies to each word on its own.
    proof fn lemma_words(x: u64, y: u64)
        ensures
            x & u64::MAX == x,
            x & 0xFFFF_FFFF == (x as u32) as u64,
            (x == y) <==> (((x >> 32) as u32) == ((y >> 32) as u32) && (x as u32) == (y as u32)),
            (x < y) <==> (((x >> 32) as u32) < ((y >> 32) as u32)
                || (((x >> 32) as u32) == ((y >> 32) as u32) && (x as u32) < (y as u32))),
            ((x & y) as u32) == ((x as u32) & (y as u32)),
            (((x & y) >> 32) as u32) == (((x >> 32) as u32) & ((y >> 32) as u32)),
    {
        assert(x & u64::MAX == x) by (bit_vector);
        assert(x & 0xFFFF_FFFF == (x as u32) as u64) by (bit_vector);
        assert(((x & y) as u32) == ((x as u32) & (y as u32))) by (bit_vector);
        assert((((x & y) >> 32) as u32) == (((x >> 32) as u32) & ((y >> 32) as u32))) by (bit_vector);
        assert((x == y) <==> (((x >> 32) as u32) == ((y >> 32) as u32) && (x as u32) == (y as u32)))
            by (bit_vector);
        assert((x < y) <==> (((x >> 32) as u32) < ((y >> 32) as u32)
            || (((x >> 32) as u32) == ((y >> 32) as u32) && (x as u32) < (y as u32)))) by (bit_vector);
    }

    /// Comparing two 64-bit patterns agrees with the two-word test on their words.
    proof fn lemma_wide_truth(self, ty: PrimType, arch: Arch, p: u64, q: u64, bias: u32)
        requires
            ty.bits(arch) == 64,
            bias == if ty.signed() && !(self is Eq) { 0x8000_0000u32 } else { 0 },
        ensures
            self.holds(ty.to_int(arch, p), ty.to_int(arch, q)) <==> self.wide_holds(
                ((p >> 32) as u32) ^ bias, p as u32, ((q >> 32) as u32) ^ bias, q as u32),
    {
        assert(ty.mask(arch) == u64::MAX);
        let hp = (p >> 32) as u32;
        let hq = (q >> 32) as u32;
        if self is Eq || !ty.signed() {
            assert(hp ^ 0u32 == hp && hq ^ 0u32 == hq) by (bit_vector);
            Self::lemma_words(p, q);
            Self::lemma_words(q, p);
            if self is Eq {
                ty.lemma_to_int_eq(arch, p, q);
            } else {
                assert(ty.to_int(arch, p) == p as int);
                assert(ty.to_int(arch, q) == q as int);
            }
        } else {
            ty.lemma_signed_bias_64(arch, p, q);
            ty.lemma_signed_bias_64(arch, q, p);
            let sign = 0x8000_0000_0000_0000u64;
            Self::lemma_words(p ^ sign, q ^ sign);
            Self::lemma_words(q ^ sign, p ^ sign);
            assert((((p ^ sign) >> 32) as u32) == hp ^ 0x8000_0000u32
                && (((q ^ sign) >> 32) as u32) == hq ^ 0x8000_0000u32
                && ((p ^ sign) as u32) == (p as u32)
                && ((q ^ sign) as u32) == (q as u32))
                by (bit_vector)
                requires sign == 0x8000_0000_0000_0000u64, hp == (p >> 32) as u32, hq == (q >> 32) as u32;
        }
    }

    /// Comparing two values agrees with the two-word test on their words, high words
    /// flipped by `0x80000000` for a signed ordering.
    proof fn lemma_pairs(self, l: &Expr, r: &Expr, arch: Arch, ctx: Seq<PrimType>, data: &[u8],
        t1: PrimType, t2: PrimType)
        requires
            l.of_type(arch, ctx, t1),
            r.of_type(arch, ctx, t2),
            t1.subtype_of(arch, t2) || t2.subtype_of(arch, t1),
        ensures ({
            let bias: u32 = if (t1.signed() || t2.signed()) && !(self is Eq) { 0x8000_0000 } else { 0 };
            self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data)) <==> self.wide_holds(
                l.word(arch, ctx, data, true) ^ bias, l.word(arch, ctx, data, false),
                r.word(arch, ctx, data, true) ^ bias, r.word(arch, ctx, data, false))
        })
    {
        l.lemma_unpat(arch, ctx, data, t1);
        r.lemma_unpat(arch, ctx, data, t2);
        let pl = l.pattern(arch, ctx, data);
        let pr = r.pattern(arch, ctx, data);
        let signed = t1.signed() || t2.signed();
        let bias: u32 = if signed && !(self is Eq) { 0x8000_0000 } else { 0 };
        // Only an unsigned operand narrower than the other meets a signed one, so both
        // read alike as signed.
        let ty = if signed { PrimType::I(64) } else { PrimType::U(64) };
        ty.lemma_unpat_64(arch, pl);
        ty.lemma_unpat_64(arch, pr);
        self.lemma_wide_truth(ty, arch, pl, pr, bias);
    }

    /// Comparing two values of types at most 32 bits wide agrees with the one-word test on
    /// their low words, flipped by `0x80000000` for a signed ordering.
    proof fn lemma_narrow(self, l: &Expr, r: &Expr, arch: Arch, ctx: Seq<PrimType>, data: &[u8],
        t1: PrimType, t2: PrimType)
        requires
            l.of_type(arch, ctx, t1),
            r.of_type(arch, ctx, t2),
            t1.subtype_of(arch, t2) || t2.subtype_of(arch, t1),
            t1.bits(arch) <= 32,
            t2.bits(arch) <= 32,
        ensures ({
            let bias: u32 = if (t1.signed() || t2.signed()) && !(self is Eq) { 0x8000_0000 } else { 0 };
            self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data)) <==> self.holds(
                (l.word(arch, ctx, data, false) ^ bias) as int, (r.word(arch, ctx, data, false) ^ bias) as int)
        })
    {
        l.lemma_unpat(arch, ctx, data, t1);
        r.lemma_unpat(arch, ctx, data, t2);
        let a = l.word(arch, ctx, data, false);
        let c = r.word(arch, ctx, data, false);
        let sign = 0x8000_0000u32;
        assert(a ^ 0u32 == a && c ^ 0u32 == c) by (bit_vector);
        // Only an unsigned operand narrower than the other meets a signed one, so both
        // read alike as signed.
        assert(((a ^ sign) < (c ^ sign)) == ((a >= sign && c < sign) || ((a >= sign) == (c >= sign) && a < c))
            && ((a ^ sign) <= (c ^ sign)) == ((a >= sign && c < sign) || ((a >= sign) == (c >= sign) && a <= c)))
            by (bit_vector)
            requires sign == 0x8000_0000u32;
    }

    /// Emits a jump to `pass` if `A` compares to `src` under this operator and to `fail`
    /// otherwise, falling through to whichever of the two is next.
    ///
    /// ```text
    ///     j<op> src -> pass/fail
    /// ```
    fn emit_jump(self, b: &mut Builder, src: Src, pass: Label, fail: Label) -> (res: Result<(), CompileError>)
        requires
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            pass == old(b).rev@.len() || fail == old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| r.wf() && self.holds(r.a as int, src.eval(r.at(0)) as int)
                ==> #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), r, pass as nat),
            res is Ok ==> forall |data: &[u8], r: Regs| r.wf() && !self.holds(r.a as int, src.eval(r.at(0)) as int)
                ==> #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), r, fail as nat),
    {
        let (jmp, expect) = self.fail_jump();
        if pass == b.label() {
            b.emit_jump(jmp, src, expect, fail)?;
        } else {
            b.emit_jump(jmp, src, !expect, pass)?;
        }
        proof {
            assert forall |data: &[u8], r: Regs|
                #![trigger Builder::lands(b.rev@, data, b.rev@.len(), r, pass as nat)]
                #![trigger Builder::lands(b.rev@, data, b.rev@.len(), r, fail as nat)]
                r.wf() implies {
                let holds = self.holds(r.a as int, src.eval(r.at(0)) as int);
                &&& holds ==> Builder::lands(b.rev@, data, b.rev@.len(), r, pass as nat)
                &&& !holds ==> Builder::lands(b.rev@, data, b.rev@.len(), r, fail as nat)
            } by {
                let to = if self.holds(r.a as int, src.eval(r.at(0)) as int) { pass } else { fail };
                assert(Builder::goes(b.rev@, data, b.rev@.len(), r, to as nat, r));
            }
        }
        Ok(())
    }

    /// Emits the jumps on the high words of a two-word test: to `fail` or `pass` if `A`
    /// and `src` differ, and on to the low words if not.
    ///
    /// ```text
    ///     jgt src -> fail         ; ordering
    ///     jne src -> pass/fail    ; pass for ordering
    /// ```
    fn emit_high(self, b: &mut Builder, src: Src, pass: Label, fail: Label) -> (res: Result<(), CompileError>)
        requires
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs, to: nat| r.wf()
                && (r.a == src.eval(r.at(0)) ==> Builder::lands(old(b).rev@, data, old(b).rev@.len(), r, to))
                && (r.a != src.eval(r.at(0)) ==>
                    to == if !(self is Eq) && r.a < src.eval(r.at(0)) { pass } else { fail })
                ==> #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), r, to),
    {
        let order = self != CmpOp::Eq;
        b.emit_jump(JmpOp::Eq, src, false, if order { pass } else { fail })?;
        let ghost r_ne = b.rev@;
        if order {
            b.emit_jump(JmpOp::Gt, src, true, fail)?;
        }
        proof {
            assert forall |data: &[u8], r: Regs, to: nat| r.wf()
                && (r.a == src.eval(r.at(0)) ==> Builder::lands(r_ne, data, r_ne.len(), r, to))
                && (r.a != src.eval(r.at(0)) ==>
                    to == if !(self is Eq) && r.a < src.eval(r.at(0)) { pass } else { fail })
                implies #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), r, to) by {
                if order && r.a > src.eval(r.at(0)) {
                    assert(Builder::goes(b.rev@, data, b.rev@.len(), r, fail as nat, r));
                }
            }
        }
        Ok(())
    }

    /// Emits a test of `lhs op rhs` on their low or high words, flipped by `bias`, that goes
    /// on to `pass` if it holds and to `fail` otherwise.
    ///
    /// ```text
    ///     <x's test against k>        ; masked_eq k, for lhs == x & m
    ///
    ///     <operands' words, bias>     ; otherwise
    ///     j<op> src -> pass/fail
    /// ```
    #[allow(clippy::too_many_arguments)]
    fn emit_test(self, b: &mut Builder, arch: Arch, Ghost(ctx): Ghost<Seq<PrimType>>, sig: &[PrimType],
        lhs: &Expr, rhs: &Expr, hi: bool, bias: u32, pass: Label, fail: Label) -> (res: Result<(), CompileError>)
        requires
            lhs.typed(arch, ctx),
            rhs.typed(arch, ctx),
            sig@ == ctx,
            self is Eq ==> bias == 0,
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            pass == old(b).rev@.len() || fail == old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && self.holds((lhs.word(arch, ctx, data, hi) ^ bias) as int,
                    (rhs.word(arch, ctx, data, hi) ^ bias) as int)
                ==> #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), st, pass as nat),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && !self.holds((lhs.word(arch, ctx, data, hi) ^ bias) as int,
                    (rhs.word(arch, ctx, data, hi) ^ bias) as int)
                ==> #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), st, fail as nat),
    {
        let masked = if self == CmpOp::Eq { lhs.masked_eq(rhs, arch, sig, hi) } else { None };
        if let (Some(k), Expr::BinOp(_, x, _)) = (masked, lhs) {
            x.emit_jset(b, arch, Ghost(ctx), sig, hi, k, pass, fail)?;
            proof {
                assert forall |data: &[u8]| #![trigger lhs.word(arch, ctx, data, hi)]
                    lhs.word(arch, ctx, data, hi) ^ 0 == lhs.word(arch, ctx, data, hi)
                    && rhs.word(arch, ctx, data, hi) ^ 0 == rhs.word(arch, ctx, data, hi) by {
                    let (wl, wr) = (lhs.word(arch, ctx, data, hi), rhs.word(arch, ctx, data, hi));
                    assert(wl ^ 0u32 == wl && wr ^ 0u32 == wr) by (bit_vector);
                }
            }
            return Ok(());
        }
        self.emit_jump(b, rhs.src(arch, hi, bias), pass, fail)?;
        let ghost r_jmp = b.rev@;
        lhs.emit_operands(rhs, b, arch, sig, hi, bias, 0)?;
        proof {
            assert forall |data: &[u8], st: Regs|
                #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)]
                #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)]
                Event::parse(data) is Some && st.wf() implies {
                let holds = self.holds((lhs.word(arch, ctx, data, hi) ^ bias) as int,
                    (rhs.word(arch, ctx, data, hi) ^ bias) as int);
                &&& holds ==> Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)
                &&& !holds ==> Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)
            } by {
                let src = rhs.src(arch, hi, bias);
                let wl = lhs.word(arch, ctx, data, hi) ^ bias;
                let wr = rhs.word(arch, ctx, data, hi) ^ bias;
                let to = if self.holds(wl as int, wr as int) { pass } else { fail };
                assert(Builder::loads2(b.rev@, data, b.rev@.len(), st, r_jmp.len(), wl, src, wr, 0));
                let t = choose |t: Regs| t.wf() && t.a == wl && src.eval(t.at(0)) == wr && t.keeps(st, 0)
                    && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_jmp.len(), t);
                assert(Builder::lands(r_jmp, data, r_jmp.len(), t, to as nat));
                Builder::lemma_then(r_jmp, b.rev@, data, b.rev@.len(), st, r_jmp.len(), t, to as nat, 0);
            }
        }
        Ok(())
    }

    /// Emits a test of `l op r` that goes on to `pass` if it holds and to `fail` otherwise.
    ///
    /// ```text
    ///     <test of low words, bias>       ; both at most 32 bits
    ///
    ///     <test of high words> -> next/fail   ; equality, low words first if theirs always passes
    /// next:
    ///     <test of low words> -> pass/fail
    ///
    ///     <operands' high words, bias>    ; ordering
    ///     jgt src -> fail
    ///     jne src -> pass
    ///     <operands' low words>
    ///     j<op> src -> pass/fail
    /// ```
    #[allow(clippy::too_many_arguments)]
    fn emit_cmp(self, b: &mut Builder, arch: Arch, Ghost(ctx): Ghost<Seq<PrimType>>, sig: &[PrimType],
        l: &Arc<Expr>, r: &Arc<Expr>, pass: Label, fail: Label) -> (res: Result<(), CompileError>)
        requires
            Cond::Cmp(self, *l, *r).wf(arch, ctx),
            sig@ == ctx,
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            pass == old(b).rev@.len() || fail == old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data)) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), st, pass as nat),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && !self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data)) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), st, fail as nat),
    {
        let ghost tys = Cond::Cmp(self, *l, *r).lemma_operand_types(arch, ctx);
        // A literal goes on the right, where it is an immediate: `k < x` is `!(x <= k)`,
        // and `k <= x` is `!(x < k)`.
        let swap = matches!(&**l, Expr::Lit(..)) && !matches!(&**r, Expr::Lit(..));
        let (op, lhs, rhs, yes, no) = if !swap {
            (self, l, r, pass, fail)
        } else {
            match self {
                CmpOp::Eq => (CmpOp::Eq, r, l, pass, fail),
                CmpOp::Lt => (CmpOp::Le, r, l, fail, pass),
                CmpOp::Le => (CmpOp::Lt, r, l, fail, pass),
            }
        };
        let ghost ty1 = if swap { tys.1 } else { tys.0 };
        let ghost ty2 = if swap { tys.0 } else { tys.1 };
        proof {
            assert(lhs.of_type(arch, ctx, ty1));
            assert(rhs.of_type(arch, ctx, ty2));
        }
        let t1 = lhs.ty(arch, sig);
        let t2 = rhs.ty(arch, sig);
        let bias: u32 = if (t1.exec_signed() || t2.exec_signed()) && op != CmpOp::Eq { 0x8000_0000 } else { 0 };
        if t1.exec_bits(arch) <= 32 && t2.exec_bits(arch) <= 32 {
            op.emit_test(b, arch, Ghost(ctx), sig, lhs, rhs, false, bias, yes, no)?;
            proof {
                assert forall |data: &[u8], st: Regs|
                    #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)]
                    #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)]
                    Event::parse(data) is Some && st.wf() implies {
                    &&& self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data))
                        ==> Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)
                    &&& !self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data))
                        ==> Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)
                } by {
                    op.lemma_narrow(lhs, rhs, arch, ctx, data, ty1, ty2);
                }
            }
        } else if op == CmpOp::Eq {
            // Equality holds word by word, so the words can go in either order, and the test
            // that comes first emits nothing if it always passes.
            let lo_first = matches!(lhs.masked_eq(rhs, arch, sig, false), Some(0));
            op.emit_test(b, arch, Ghost(ctx), sig, lhs, rhs, lo_first, 0, yes, no)?;
            let ghost r_last = b.rev@;
            let next = b.label();
            op.emit_test(b, arch, Ghost(ctx), sig, lhs, rhs, !lo_first, 0, next, no)?;
            proof {
                assert forall |data: &[u8], st: Regs|
                    #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)]
                    #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)]
                    Event::parse(data) is Some && st.wf() implies {
                    &&& self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data))
                        ==> Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)
                    &&& !self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data))
                        ==> Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)
                } by {
                    let (hl, ll) = (lhs.word(arch, ctx, data, true), lhs.word(arch, ctx, data, false));
                    let (hr, lr) = (rhs.word(arch, ctx, data, true), rhs.word(arch, ctx, data, false));
                    op.lemma_pairs(lhs, rhs, arch, ctx, data, ty1, ty2);
                    assert(hl ^ 0u32 == hl && hr ^ 0u32 == hr && ll ^ 0u32 == ll && lr ^ 0u32 == lr)
                        by (bit_vector);
                    let holds = hl == hr && ll == lr;
                    let to = if holds { yes } else { no };
                    if lhs.word(arch, ctx, data, !lo_first) == rhs.word(arch, ctx, data, !lo_first) {
                        assert(Builder::lands(b.rev@, data, b.rev@.len(), st, next as nat));
                        let m = choose |m: Regs| m.wf()
                            && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, next as nat, m);
                        assert(Builder::lands(r_last, data, next as nat, m, to as nat));
                        Builder::lemma_then(r_last, b.rev@, data, b.rev@.len(), st, next as nat, m, to as nat, 0);
                    }
                }
            }
        } else {
            op.emit_jump(b, rhs.src(arch, false, 0), yes, no)?;
            let ghost r_jmp = b.rev@;
            lhs.emit_operands(rhs, b, arch, sig, false, 0, 0)?;
            let ghost r_low = b.rev@;
            op.emit_high(b, rhs.src(arch, true, bias), yes, no)?;
            let ghost r_high = b.rev@;
            lhs.emit_operands(rhs, b, arch, sig, true, bias, 0)?;
            proof {
                assert forall |data: &[u8], st: Regs|
                    #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)]
                    #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)]
                    Event::parse(data) is Some && st.wf() implies {
                    &&& self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data))
                        ==> Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)
                    &&& !self.holds(l.value(arch, ctx, data), r.value(arch, ctx, data))
                        ==> Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)
                } by {
                    let (lsrc, hsrc) = (rhs.src(arch, false, 0), rhs.src(arch, true, bias));
                    let (hl, ll) = (lhs.word(arch, ctx, data, true), lhs.word(arch, ctx, data, false));
                    let (hr, lr) = (rhs.word(arch, ctx, data, true), rhs.word(arch, ctx, data, false));
                    let holds = op.holds(lhs.value(arch, ctx, data), rhs.value(arch, ctx, data));
                    let to = if holds { yes } else { no };
                    op.lemma_pairs(lhs, rhs, arch, ctx, data, ty1, ty2);
                    assert(ll ^ 0u32 == ll && lr ^ 0u32 == lr) by (bit_vector);
                    assert(Builder::loads2(b.rev@, data, b.rev@.len(), st, r_high.len(), hl ^ bias, hsrc,
                        hr ^ bias, 0));
                    let t1 = choose |t1: Regs| t1.wf() && t1.a == hl ^ bias && hsrc.eval(t1.at(0)) == hr ^ bias
                        && t1.keeps(st, 0)
                        && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_high.len(), t1);
                    if hl ^ bias == hr ^ bias {
                        assert(Builder::loads2(r_low, data, r_low.len(), t1, r_jmp.len(), ll ^ 0, lsrc, lr ^ 0, 0));
                        let t2 = choose |t2: Regs| t2.wf() && t2.a == ll ^ 0 && lsrc.eval(t2.at(0)) == lr ^ 0
                            && t2.keeps(t1, 0)
                            && #[trigger] Builder::goes(r_low, data, r_low.len(), t1, r_jmp.len(), t2);
                        if holds {
                            assert(Builder::lands(r_jmp, data, r_jmp.len(), t2, yes as nat));
                        } else {
                            assert(Builder::lands(r_jmp, data, r_jmp.len(), t2, no as nat));
                        }
                        Builder::lemma_then(r_jmp, r_low, data, r_low.len(), t1, r_jmp.len(), t2, to as nat, 0);
                    }
                    assert(Builder::lands(r_high, data, r_high.len(), t1, to as nat));
                    Builder::lemma_then(r_high, b.rev@, data, b.rev@.len(), st, r_high.len(), t1, to as nat, 0);
                }
            }
        }
        Ok(())
    }
}

impl Expr {
    /// The value of this expression on the event `data` describes, with arguments read by
    /// signature `ctx`.
    pub(super) open spec fn value(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8]) -> int {
        self.eval(arch, ctx, arch.interp_args(Event::of(data).args, ctx))
    }

    /// The types an expression can have agree on width and signedness.
    pub(crate) proof fn lemma_type_unique(&self, arch: Arch, ctx: Seq<PrimType>, t1: PrimType, t2: PrimType)
        requires self.of_type(arch, ctx, t1), self.of_type(arch, ctx, t2)
        ensures t1.bits(arch) == t2.bits(arch), t1.signed() == t2.signed()
        decreases self
    {
        match self {
            Expr::BinOp(op, e1, e2) => if *op is Add || *op is Sub {
                let (a1, b1) = self.lemma_operands(arch, ctx, t1);
                let (a2, b2) = self.lemma_operands(arch, ctx, t2);
                e1.lemma_type_unique(arch, ctx, a1, a2);
                e2.lemma_type_unique(arch, ctx, b1, b2);
            } else {
                assert(e1.of_type(arch, ctx, t1));
                assert(e1.of_type(arch, ctx, t2));
                e1.lemma_type_unique(arch, ctx, t1, t2);
            },
            _ => {}
        }
    }

    /// Returns the types of the operands of a sum or difference of type `ty`.
    pub(crate) proof fn lemma_operands(&self, arch: Arch, ctx: Seq<PrimType>, ty: PrimType) -> (tys: (PrimType, PrimType))
        requires self is BinOp, self->BinOp_0 is Add || self->BinOp_0 is Sub, self.of_type(arch, ctx, ty)
        ensures
            self->BinOp_1.of_type(arch, ctx, tys.0),
            self->BinOp_2.of_type(arch, ctx, tys.1),
            tys.0.subtype_of(arch, tys.1) && ty == tys.1 || tys.1.subtype_of(arch, tys.0) && ty == tys.0,
    {
        choose |a: PrimType, b: PrimType| #![trigger a.subtype_of(arch, b)] {
            &&& self->BinOp_1.of_type(arch, ctx, a)
            &&& self->BinOp_2.of_type(arch, ctx, b)
            &&& a.subtype_of(arch, b) && ty == b || b.subtype_of(arch, a) && ty == a
        }
    }

    /// Returns, if this is `x & m` for a literal `m` and `other` is a literal whose word is
    /// zero, the bits `k` of `m` such that the two words are equal exactly when `x`'s word
    /// has none of them set.
    fn masked_eq(&self, other: &Expr, arch: Arch, sig: &[PrimType], hi: bool) -> (res: Option<u32>)
        requires self.typed(arch, sig@), other.typed(arch, sig@)
        ensures
            res is Some ==> self is BinOp && self->BinOp_1.typed(arch, sig@),
            res is Some ==> forall |data: &[u8]| #![trigger self.word(arch, sig@, data, hi)]
                (self.word(arch, sig@, data, hi) == other.word(arch, sig@, data, hi))
                    == (self->BinOp_1.word(arch, sig@, data, hi) & res->Some_0 == 0),
    {
        proof { self.lemma_operands_typed(arch, sig@); }
        if let Expr::BinOp(BinOp::And, _, m) = self {
            if let Src::K(k) = m.src(arch, hi, 0) {
                let ty = self.ty(arch, sig);
                if other.src(arch, hi, 0) == Src::K(0) && (!hi || ty.exec_bits(arch) == 64) {
                    let mask = ty.exec_mask(arch);
                    let k = k & if hi { (mask >> 32) as u32 } else { mask as u32 };
                    proof {
                        assert forall |data: &[u8]| #![trigger self.word(arch, sig@, data, hi)]
                            (self.word(arch, sig@, data, hi) == other.word(arch, sig@, data, hi))
                                == (self->BinOp_1.word(arch, sig@, data, hi) & k == 0) by {
                            self.lemma_and_word(arch, sig@, data, ty, hi);
                            let (wm, wo) = (m.word(arch, sig@, data, hi), other.word(arch, sig@, data, hi));
                            assert(wm ^ 0u32 == wm && wo ^ 0u32 == wo) by (bit_vector);
                        }
                    }
                    return Some(k);
                }
            }
        }
        None
    }

    /// Emits a test that goes on to `pass` if this expression's low or high word has no bit
    /// of `k` set and to `fail` otherwise.
    ///
    /// ```text
    ///                             ; k == 0 and pass next, emits nothing
    ///
    ///     <word>                  ; otherwise
    ///     jset #k -> fail/pass
    /// ```
    #[allow(clippy::too_many_arguments)]
    fn emit_jset(&self, b: &mut Builder, arch: Arch, Ghost(ctx): Ghost<Seq<PrimType>>, sig: &[PrimType],
        hi: bool, k: u32, pass: Label, fail: Label) -> (res: Result<(), CompileError>)
        requires
            self.typed(arch, ctx),
            sig@ == ctx,
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            pass == old(b).rev@.len() || fail == old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && self.word(arch, ctx, data, hi) & k == 0
                ==> #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), st, pass as nat),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && self.word(arch, ctx, data, hi) & k != 0
                ==> #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), st, fail as nat),
    {
        if k == 0 && pass == b.label() {
            proof {
                assert forall |data: &[u8], st: Regs| st.wf() implies
                    #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat) by {
                    assert(Builder::goes(b.rev@, data, b.rev@.len(), st, pass as nat, st));
                }
                assert forall |data: &[u8]| #![trigger self.word(arch, ctx, data, hi)]
                    self.word(arch, ctx, data, hi) & k == 0 by {
                    let w = self.word(arch, ctx, data, hi);
                    assert(w & 0 == 0) by (bit_vector);
                }
            }
            return Ok(());
        }
        if pass == b.label() {
            b.emit_jump(JmpOp::Set, Src::K(k), true, fail)?;
        } else {
            b.emit_jump(JmpOp::Set, Src::K(k), false, pass)?;
        }
        let ghost r_jmp = b.rev@;
        self.emit_word(b, arch, sig, hi, 0, 0)?;
        proof {
            assert forall |data: &[u8], st: Regs|
                #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)]
                #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)]
                Event::parse(data) is Some && st.wf() implies {
                let clear = self.word(arch, ctx, data, hi) & k == 0;
                &&& clear ==> Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)
                &&& !clear ==> Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)
            } by {
                let w = self.word(arch, ctx, data, hi);
                assert(w ^ 0u32 == w) by (bit_vector);
                let to = if w & k == 0 { pass } else { fail };
                assert(Builder::loads(b.rev@, data, b.rev@.len(), st, r_jmp.len(), w ^ 0, 0));
                let t = choose |t: Regs| t.wf() && t.a == w ^ 0 && t.keeps(st, 0)
                    && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_jmp.len(), t);
                assert(t.test(JmpOp::Set, Src::K(k)) == (w & k != 0));
                assert(Builder::goes(r_jmp, data, r_jmp.len(), t, to as nat, t));
                Builder::lemma_then(r_jmp, b.rev@, data, b.rev@.len(), st, r_jmp.len(), t, to as nat, 0);
            }
        }
        Ok(())
    }
}

impl Cond {
    /// Whether this condition holds on the event `data` describes, with arguments read by
    /// signature `ctx`.
    pub(super) open spec fn holds(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8]) -> bool {
        self.eval(arch, ctx, arch.interp_args(Event::of(data).args, ctx))
    }

    /// Emits a test that goes on to `pass` if this condition holds and to `fail` otherwise,
    /// and returns where the test starts.
    ///
    /// ```text
    ///     <l> -> r/fail           ; l && r
    /// r:  <r> -> pass/fail
    ///
    ///     <l> -> pass/r           ; l || r
    /// r:  <r> -> pass/fail
    ///
    ///     <c> -> fail/pass        ; !c
    ///
    ///     <l op r> -> pass/fail   ; l op r
    ///     ja  pass                ; neither pass nor fail is next
    ///
    ///                             ; true and false emit nothing and start at pass or fail
    /// ```
    pub(super) fn emit(&self, b: &mut Builder, arch: Arch, Ghost(ctx): Ghost<Seq<PrimType>>,
        sig: &[PrimType], pass: Label, fail: Label) -> (res: Result<Label, CompileError>)
        requires
            self.wf(arch, ctx),
            sig@ == ctx,
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res matches Ok(entry) ==> 0 < entry <= final(b).rev@.len(),
            res matches Ok(entry) ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && self.holds(arch, ctx, data) ==>
                #[trigger] Builder::lands(final(b).rev@, data, entry as nat, st, pass as nat),
            res matches Ok(entry) ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && !self.holds(arch, ctx, data) ==>
                #[trigger] Builder::lands(final(b).rev@, data, entry as nat, st, fail as nat),
        decreases self
    {
        match self {
            Cond::True | Cond::False => {
                proof {
                    assert forall |data: &[u8], st: Regs, at: nat| st.wf() implies
                        #[trigger] Builder::lands(b.rev@, data, at, st, at) by {
                        assert(Builder::goes(b.rev@, data, at, st, at, st));
                    }
                }
                Ok(if matches!(self, Cond::True) { pass } else { fail })
            }
            Cond::And(l, r) | Cond::Or(l, r) => {
                let mid = r.emit(b, arch, Ghost(ctx), sig, pass, fail)?;
                let ghost r_mid = b.rev@;
                let (l_pass, l_fail) = if matches!(self, Cond::And(..)) { (mid, fail) } else { (pass, mid) };
                let entry = l.emit(b, arch, Ghost(ctx), sig, l_pass, l_fail)?;
                proof {
                    assert forall |data: &[u8], st: Regs|
                        #![trigger Builder::lands(b.rev@, data, entry as nat, st, pass as nat)]
                        #![trigger Builder::lands(b.rev@, data, entry as nat, st, fail as nat)]
                        Event::parse(data) is Some && st.wf() implies {
                        &&& self.holds(arch, ctx, data) ==>
                            Builder::lands(b.rev@, data, entry as nat, st, pass as nat)
                        &&& !self.holds(arch, ctx, data) ==>
                            Builder::lands(b.rev@, data, entry as nat, st, fail as nat)
                    } by {
                        if l.holds(arch, ctx, data) == self is And {
                            assert(Builder::lands(b.rev@, data, entry as nat, st, mid as nat));
                            let m = choose |m: Regs| m.wf()
                                && #[trigger] Builder::goes(b.rev@, data, entry as nat, st, mid as nat, m);
                            assert(Builder::lands(r_mid, data, mid as nat, m, pass as nat)
                                || !r.holds(arch, ctx, data));
                            assert(Builder::lands(r_mid, data, mid as nat, m, fail as nat)
                                || r.holds(arch, ctx, data));
                            Builder::lemma_then(r_mid, b.rev@, data, entry as nat, st, mid as nat, m, pass as nat, 0);
                            Builder::lemma_then(r_mid, b.rev@, data, entry as nat, st, mid as nat, m, fail as nat, 0);
                        }
                    }
                }
                Ok(entry)
            }
            Cond::Not(c) => c.emit(b, arch, Ghost(ctx), sig, fail, pass),
            Cond::Cmp(op, l, r) => {
                // The last jump falls through to one of the test's two ends, so one of them
                // has to come next.
                let (pass_at, fail_at) = if pass == b.label() || fail == b.label() {
                    (pass, fail)
                } else {
                    b.emit_goto(pass)?;
                    (b.label(), fail)
                };
                let ghost r_goto = b.rev@;
                op.emit_cmp(b, arch, Ghost(ctx), sig, l, r, pass_at, fail_at)?;
                proof {
                    assert forall |data: &[u8], st: Regs|
                        #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)]
                        #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)]
                        Event::parse(data) is Some && st.wf() implies {
                        &&& self.holds(arch, ctx, data) ==>
                            Builder::lands(b.rev@, data, b.rev@.len(), st, pass as nat)
                        &&& !self.holds(arch, ctx, data) ==>
                            Builder::lands(b.rev@, data, b.rev@.len(), st, fail as nat)
                    } by {
                        if pass_at != pass && self.holds(arch, ctx, data) {
                            assert(Builder::lands(b.rev@, data, b.rev@.len(), st, pass_at as nat));
                            let m = choose |m: Regs| m.wf()
                                && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, pass_at as nat, m);
                            assert(Builder::goes(r_goto, data, pass_at as nat, m, pass as nat, m));
                            Builder::lemma_then(r_goto, b.rev@, data, b.rev@.len(), st, pass_at as nat, m, pass as nat, 0);
                        }
                    }
                }
                Ok(b.label())
            }
        }
    }

    /// Returns the types of the operands of a well-typed comparison.
    proof fn lemma_operand_types(&self, arch: Arch, ctx: Seq<PrimType>) -> (tys: (PrimType, PrimType))
        requires self is Cmp, self.wf(arch, ctx)
        ensures
            self->Cmp_1.of_type(arch, ctx, tys.0),
            self->Cmp_2.of_type(arch, ctx, tys.1),
            tys.0.subtype_of(arch, tys.1) || tys.1.subtype_of(arch, tys.0),
    {
        choose |ty1: PrimType, ty2: PrimType| #![trigger ty1.subtype_of(arch, ty2)]
            self->Cmp_1.of_type(arch, ctx, ty1) && self->Cmp_2.of_type(arch, ctx, ty2)
            && (ty1.subtype_of(arch, ty2) || ty2.subtype_of(arch, ty1))
    }
}

} // verus!
