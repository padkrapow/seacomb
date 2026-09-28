//! Compiling rule conditions: the jumps that combine them, and the word tests at their leaves.

use vstd::prelude::*;
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

    /// Executable version of [`PrimType::to_bits`] on a literal.
    fn lit_bits(self, arch: Arch, c: i64) -> (res: u64)
        ensures
            res == self.to_bits(arch, c as int),
            res & !self.mask(arch) == 0,
    {
        // The 64-bit two's complement word of `c`.
        let word = if c >= 0 { c as u64 } else { u64::MAX - (-(c + 1)) as u64 };
        let mask = self.exec_mask(arch);
        proof {
            self.lemma_to_bits_wrap(arch, c as int, word);
            assert((word & mask) & !mask == 0) by (bit_vector);
        }
        word & mask
    }

    /// Reducing anything congruent to `u` modulo `2^64` leaves the low bits of `u`.
    proof fn lemma_to_bits_wrap(self, arch: Arch, v: int, u: u64)
        requires v == u as int || v == u as int - 0x1_0000_0000_0000_0000
        ensures self.to_bits(arch, v) == u & self.mask(arch)
    {
        let bits = self.bits(arch);
        let mask = self.mask(arch);
        if bits >= 64 {
            assert(u & u64::MAX == u) by (bit_vector);
            vstd::arithmetic::div_mod::lemma_small_mod(u as nat, 0x1_0000_0000_0000_0000);
            if v != u as int {
                vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(
                    u as int, 0x1_0000_0000_0000_0000);
            }
        } else {
            let m = vstd::arithmetic::power2::pow2(bits as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(bits as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, bits);
            vstd::bits::lemma_u64_low_bits_mask_is_mod(u, bits as nat);
            assert(mask as int + 1 == m);
            if v != u as int {
                let k = vstd::arithmetic::power2::pow2((64 - bits) as nat) as int;
                vstd::arithmetic::power2::lemma_pow2_adds(bits as nat, (64 - bits) as nat);
                vstd::arithmetic::power2::lemma2_to64();
                assert(m * (-k) == -(m * k)) by (nonlinear_arith);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-k, u as int, m as int);
            }
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

    /// The bits outside this type's mask do not change what it reads.
    proof fn lemma_to_int_mask(self, arch: Arch, x: u64)
        ensures self.to_int(arch, x & self.mask(arch)) == self.to_int(arch, x)
    {
        let mask = self.mask(arch);
        assert((x & mask) & mask == x & mask) by (bit_vector);
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

    /// Flipping the sign bit turns signed narrow ordering into unsigned ordering.
    proof fn lemma_signed_bias(self, arch: Arch, x: u64, y: u64)
        requires
            self.signed(),
            self.bits(arch) == 16 || self.bits(arch) == 32,
        ensures
            (self.to_int(arch, x) < self.to_int(arch, y)) <==> {
                let mask = self.mask(arch);
                let bias = ((mask >> 1u64) + 1) as u64;
                (((x & mask) ^ bias) as u32) < (((y & mask) ^ bias) as u32)
            },
    {
        let mask = self.mask(arch);
        let half = mask >> 1u64;
        let bias: u64 = (half + 1) as u64;
        let px = x & mask;
        let py = y & mask;
        if self.bits(arch) == 16 {
            assert(((1u64 << 16u64) - 1) == 0xFFFF) by (bit_vector);
            assert(mask == 0xFFFF);
            assert((mask >> 1u64) == 0x7FFF) by (bit_vector)
                requires mask == 0xFFFF;
        } else {
            assert(((1u64 << 32u64) - 1) == 0xFFFF_FFFF) by (bit_vector);
            assert(mask == 0xFFFF_FFFF);
            assert((mask >> 1u64) == 0x7FFF_FFFF) by (bit_vector)
                requires mask == 0xFFFF_FFFF;
        }
        assert((x & mask) <= mask) by (bit_vector);
        assert((y & mask) <= mask) by (bit_vector);
        assert(((px ^ bias) as u32) < ((py ^ bias) as u32) <==>
            ((px > half && py <= half) || ((px > half) == (py > half) && px < py)))
            by (bit_vector)
            requires mask == 0xFFFF || mask == 0xFFFF_FFFF,
                half == mask >> 1u64, bias == half + 1,
                px == x & mask, py == y & mask;
        if px > half {
            if py > half {
                assert(self.to_int(arch, x) == px as int - (mask as int + 1));
                assert(self.to_int(arch, y) == py as int - (mask as int + 1));
            }
        } else if py > half {
            assert(self.to_int(arch, x) == px as int);
            assert(self.to_int(arch, y) == py as int - (mask as int + 1));
        }
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

    /// Comparing two narrow patterns agrees with the one-word test on their words.
    proof fn lemma_word_truth(self, ty: PrimType, arch: Arch, p: u64, q: u64, bias: u32)
        requires
            ty.bits(arch) == 16 || ty.bits(arch) == 32,
            p & !ty.mask(arch) == 0,
            q & !ty.mask(arch) == 0,
            bias == if ty.signed() && !(self is Eq) {
                if ty.bits(arch) == 16 { 0x8000u32 } else { 0x8000_0000u32 }
            } else { 0 },
        ensures
            self.holds(ty.to_int(arch, p), ty.to_int(arch, q))
                <==> self.holds(((p as u32) ^ bias) as int, ((q as u32) ^ bias) as int),
    {
        let mask = ty.mask(arch);
        if ty.bits(arch) == 16 {
            assert(((1u64 << 16u64) - 1) == 0xFFFF) by (bit_vector);
        } else {
            assert(((1u64 << 32u64) - 1) == 0xFFFF_FFFF) by (bit_vector);
        }
        let pw = p as u32;
        let qw = q as u32;
        assert(p & mask == p && q & mask == q && pw as u64 == p && qw as u64 == q) by (bit_vector)
            requires p & !mask == 0, q & !mask == 0, mask == 0xFFFF || mask == 0xFFFF_FFFF,
                pw == p as u32, qw == q as u32;
        if self is Eq || !ty.signed() {
            assert(pw ^ 0u32 == pw && qw ^ 0u32 == qw) by (bit_vector);
            if self is Eq {
                ty.lemma_to_int_eq(arch, p, q);
            }
        } else {
            ty.lemma_signed_bias(arch, p, q);
            ty.lemma_signed_bias(arch, q, p);
            if ty.bits(arch) == 16 {
                assert((mask >> 1u64) == 0x7FFF) by (bit_vector) requires mask == 0xFFFF;
            } else {
                assert((mask >> 1u64) == 0x7FFF_FFFF) by (bit_vector) requires mask == 0xFFFF_FFFF;
            }
            let b64 = ((mask >> 1u64) + 1) as u64;
            assert(b64 == bias as u64);
            assert((((p & mask) ^ b64) as u32) == pw ^ bias && (((q & mask) ^ b64) as u32) == qw ^ bias)
                by (bit_vector)
                requires p & mask == p, q & mask == q, b64 == bias as u64,
                    pw == p as u32, qw == q as u32;
        }
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

    /// Emits a test of a 64-bit value whose high word is at `hi` and low word at `lo`,
    /// going on to `pass` if it holds and to `fail` otherwise.
    ///
    /// ```text
    ///     ld  [hi]
    ///     and #mask_hi            ; mask_hi != 0xffffffff
    ///     xor #bias               ; bias != 0
    ///     jgt #k_hi -> fail       ; ordering
    ///     jne #k_hi -> pass/fail  ; pass for ordering
    ///     ld  [lo]
    ///     and #mask_lo            ; mask_lo != 0xffffffff
    ///     j<op> #k_lo -> pass/fail
    /// ```
    #[allow(clippy::too_many_arguments)]
    fn emit_wide(self, b: &mut Builder, lo: u32, hi: u32, mask_lo: u32, mask_hi: u32, bias: u32,
        k_lo: u32, k_hi: u32, pass: Label, fail: Label) -> (res: Result<(), CompileError>)
        requires
            lo % 4 == 0,
            hi % 4 == 0,
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            pass == old(b).rev@.len() || fail == old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| lo + 4 <= data@.len() && hi + 4 <= data@.len() && r.wf()
                && self.wide_holds((Builder::word(data, hi) & mask_hi) ^ bias,
                    Builder::word(data, lo) & mask_lo, k_hi, k_lo) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), r, pass as nat),
            res is Ok ==> forall |data: &[u8], r: Regs| lo + 4 <= data@.len() && hi + 4 <= data@.len() && r.wf()
                && !self.wide_holds((Builder::word(data, hi) & mask_hi) ^ bias,
                    Builder::word(data, lo) & mask_lo, k_hi, k_lo) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), r, fail as nat),
    {
        self.emit_jump(b, Src::K(k_lo), pass, fail)?;
        b.emit_load(lo, mask_lo, 0);
        let ghost r_lo = b.rev@;
        self.emit_high(b, Src::K(k_hi), pass, fail)?;
        let ghost r_gt = b.rev@;
        b.emit_load(hi, mask_hi, bias);
        proof {
            assert forall |data: &[u8], r: Regs|
                #![trigger Builder::lands(r_gt, data, r_gt.len(), r, pass as nat)]
                #![trigger Builder::lands(r_gt, data, r_gt.len(), r, fail as nat)]
                lo + 4 <= data@.len() && r.wf() implies {
                let lw = Builder::word(data, lo) & mask_lo;
                &&& self.wide_holds(r.a, lw, k_hi, k_lo) ==> Builder::lands(r_gt, data, r_gt.len(), r, pass as nat)
                &&& !self.wide_holds(r.a, lw, k_hi, k_lo) ==> Builder::lands(r_gt, data, r_gt.len(), r, fail as nat)
            } by {
                let lw = Builder::word(data, lo) & mask_lo;
                assert((lw ^ 0u32) == lw) by (bit_vector);
                let to = if self.wide_holds(r.a, lw, k_hi, k_lo) { pass as nat } else { fail as nat };
                if r.a == k_hi {
                    assert(Builder::lands(r_lo, data, r_lo.len(), r, to));
                }
                assert(Builder::lands(r_gt, data, r_gt.len(), r, to));
            }
        }
        Ok(())
    }

    /// Emits a test of the patterns in scratch pairs 0 and 1, their high words flipped by
    /// `bias`, that goes on to `pass` if it holds and to `fail` otherwise.
    ///
    /// ```text
    ///     ld  M[3]
    ///     xor #bias               ; bias != 0
    ///     tax
    ///     ld  M[1]
    ///     xor #bias               ; bias != 0
    ///     jgt x -> fail           ; ordering
    ///     jne x -> pass/fail      ; pass for ordering
    ///     ldx M[2]
    ///     ld  M[0]
    ///     j<op> x -> pass/fail
    /// ```
    pub(super) fn emit_pairs(self, b: &mut Builder, bias: u32, pass: Label, fail: Label)
        -> (res: Result<(), CompileError>)
        requires
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            pass == old(b).rev@.len() || fail == old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], t: Regs, pl: u64, pr: u64|
                #![trigger t.holds(0, pl), t.holds(1, pr),
                    Builder::lands(final(b).rev@, data, final(b).rev@.len(), t, pass as nat)]
                t.wf() && t.holds(0, pl) && t.holds(1, pr)
                && self.wide_holds(((pl >> 32) as u32) ^ bias, pl as u32, ((pr >> 32) as u32) ^ bias, pr as u32) ==>
                Builder::lands(final(b).rev@, data, final(b).rev@.len(), t, pass as nat),
            res is Ok ==> forall |data: &[u8], t: Regs, pl: u64, pr: u64|
                #![trigger t.holds(0, pl), t.holds(1, pr),
                    Builder::lands(final(b).rev@, data, final(b).rev@.len(), t, fail as nat)]
                t.wf() && t.holds(0, pl) && t.holds(1, pr)
                && !self.wide_holds(((pl >> 32) as u32) ^ bias, pl as u32, ((pr >> 32) as u32) ^ bias, pr as u32) ==>
                Builder::lands(final(b).rev@, data, final(b).rev@.len(), t, fail as nat),
    {
        self.emit_jump(b, Src::X, pass, fail)?;
        let ghost r_jmp = b.rev@;
        let low = [Instr::LdxMem(2), Instr::LdMem(0)];
        proof { reveal_with_fuel(Instr::fits_from, 3); }
        b.emit_block(&low);
        let ghost r_low = b.rev@;
        self.emit_high(b, Src::X, pass, fail)?;
        let ghost r_gt = b.rev@;
        let ghost high = |t: Regs, pl: u64, pr: u64|
            Regs { a: ((pl >> 32) as u32) ^ bias, x: ((pr >> 32) as u32) ^ bias, mem: t.mem };
        let block: &[Instr] = if bias != 0 {
            &[Instr::LdMem(3), Instr::Alu(AluOp::Xor, Src::K(bias)), Instr::Tax,
                Instr::LdMem(1), Instr::Alu(AluOp::Xor, Src::K(bias))]
        } else {
            &[Instr::LdMem(3), Instr::Tax, Instr::LdMem(1)]
        };
        proof { reveal_with_fuel(Instr::fits_from, 6); }
        b.emit_block(block);
        proof {
            assert forall |data: &[u8], t: Regs, pl: u64, pr: u64|
                t.wf() && t.holds(0, pl) && t.holds(1, pr) implies
                #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), t, r_gt.len(), high(t, pl, pr)) by {
                let (hl, hr) = ((pl >> 32) as u32, (pr >> 32) as u32);
                assert(hl ^ 0u32 == hl && hr ^ 0u32 == hr) by (bit_vector);
                reveal_with_fuel(Instr::exec_block, 6);
                assert(Instr::exec_block(block@, 0, data, t) == Some(high(t, pl, pr)));
            }
        }
        proof {
            assert forall |data: &[u8], t: Regs, pl: u64, pr: u64|
                #![trigger t.holds(0, pl), t.holds(1, pr),
                    Builder::lands(b.rev@, data, b.rev@.len(), t, pass as nat)]
                #![trigger t.holds(0, pl), t.holds(1, pr),
                    Builder::lands(b.rev@, data, b.rev@.len(), t, fail as nat)]
                t.wf() && t.holds(0, pl) && t.holds(1, pr) implies {
                let holds = self.wide_holds(((pl >> 32) as u32) ^ bias, pl as u32, ((pr >> 32) as u32) ^ bias, pr as u32);
                &&& holds ==> Builder::lands(b.rev@, data, b.rev@.len(), t, pass as nat)
                &&& !holds ==> Builder::lands(b.rev@, data, b.rev@.len(), t, fail as nat)
            } by {
                let (hl, hr) = ((pl >> 32) as u32, (pr >> 32) as u32);
                let h = high(t, pl, pr);
                let lw = Regs { a: pl as u32, x: pr as u32, mem: t.mem };
                let holds = self.wide_holds(hl ^ bias, pl as u32, hr ^ bias, pr as u32);
                let to = if holds { pass as nat } else { fail as nat };
                assert((hl ^ bias == hr ^ bias) == (hl == hr)) by (bit_vector);
                assert(Builder::goes(b.rev@, data, b.rev@.len(), t, r_gt.len(), h));
                if hl == hr {
                    reveal_with_fuel(Instr::exec_block, 3);
                    assert(Instr::exec_block(low@, 0, data, h) == Some(lw));
                    assert(Builder::goes(r_low, data, r_low.len(), h, r_jmp.len(), lw));
                    Builder::lemma_then(r_jmp, r_low, data, r_low.len(), h, r_jmp.len(), lw, to, 0);
                }
                assert(Builder::lands(r_gt, data, r_gt.len(), h, to));
                Builder::lemma_then(r_gt, b.rev@, data, b.rev@.len(), t, r_gt.len(), h, to, 0);
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

    /// The argument this expression reads, the type it reads it at, and the mask it puts on
    /// its bits, if it is such a masked read.
    spec fn spec_term(&self, arch: Arch, ctx: Seq<PrimType>) -> Option<(u32, PrimType, u64)>
        decreases self
    {
        match *self {
            Expr::Var(i) => if i < ctx.len() { Some((i, ctx[i as int], u64::MAX)) } else { None },
            Expr::Cast(e, t) => match e.spec_term(arch, ctx) {
                Some((i, s, m)) => if s.bits(arch) == t.bits(arch) { Some((i, t, m)) } else { None },
                None => None,
            },
            Expr::BinOp(BinOp::And, e, c) => match *c {
                Expr::Lit(v, t) => match e.spec_term(arch, ctx) {
                    Some((i, _, m)) => Some((i, t, m & t.to_bits(arch, v as int))),
                    None => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// Executable version of [`Expr::spec_term`].
    #[allow(clippy::manual_map)]
    fn term(&self, arch: Arch, sig: &[PrimType]) -> (res: Option<(u32, PrimType, u64)>)
        ensures res == self.spec_term(arch, sig@)
        decreases self
    {
        match self {
            Expr::Var(i) => if (*i as usize) < sig.len() { Some((*i, sig[*i as usize], u64::MAX)) } else { None },
            Expr::Cast(e, t) => match e.term(arch, sig) {
                Some((i, s, m)) => if s.exec_bits(arch) == t.exec_bits(arch) { Some((i, *t, m)) } else { None },
                None => None,
            },
            Expr::BinOp(BinOp::And, e, c) => match &**c {
                Expr::Lit(v, t) => match e.term(arch, sig) {
                    Some((i, _, m)) => Some((i, *t, m & t.lit_bits(arch, *v))),
                    None => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// The types an expression can have agree on width and signedness.
    pub(super) proof fn lemma_type_unique(&self, arch: Arch, ctx: Seq<PrimType>, t1: PrimType, t2: PrimType)
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
    pub(super) proof fn lemma_operands(&self, arch: Arch, ctx: Seq<PrimType>, ty: PrimType) -> (tys: (PrimType, PrimType))
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

    /// A masked read evaluates to its mask applied to the bits of the argument it reads.
    proof fn lemma_term(&self, arch: Arch, ctx: Seq<PrimType>, args: Seq<u64>, ty: PrimType)
        requires self.spec_term(arch, ctx) is Some, self.of_type(arch, ctx, ty)
        ensures ({
            let term = self.spec_term(arch, ctx)->Some_0;
            &&& ty == term.1
            &&& term.0 < ctx.len()
            &&& ctx[term.0 as int].bits(arch) == term.1.bits(arch)
            &&& self.eval(arch, ctx, args) == term.1.to_int(arch, args[term.0 as int] & term.2)
        })
        decreases self
    {
        match self {
            Expr::Var(i) => {
                let x = args[*i as int];
                assert(x & u64::MAX == x) by (bit_vector);
            }
            Expr::Cast(e, t) => {
                let inner = e.spec_term(arch, ctx)->Some_0;
                reveal_with_fuel(Expr::of_type, 3);
                assert(e.of_type(arch, ctx, inner.1));
                e.lemma_term(arch, ctx, args, inner.1);
                let p = args[inner.0 as int] & inner.2;
                inner.1.lemma_to_int_bits(arch, p);
                t.lemma_to_int_mask(arch, p);
                assert(ty == *t);
                assert(e.eval(arch, ctx, args) == inner.1.to_int(arch, p));
                assert(inner.1.mask(arch) == t.mask(arch));
                assert(t.to_bits(arch, e.eval(arch, ctx, args)) == p & t.mask(arch));
                assert(self.eval(arch, ctx, args) == t.to_int(arch, p));
            }
            Expr::BinOp(BinOp::And, e, c) => {
                match **c {
                    Expr::Lit(v, t) => {
                        let inner = e.spec_term(arch, ctx)->Some_0;
                        assert(c.of_type(arch, ctx, ty));
                        assert(e.of_type(arch, ctx, ty));
                        e.lemma_term(arch, ctx, args, ty);
                        let cty = choose |cty: PrimType| self.of_type(arch, ctx, cty);
                        assert(c.of_type(arch, ctx, cty));
                        let x = args[inner.0 as int];
                        let m = inner.2;
                        let mask = t.mask(arch);
                        let lit = t.to_bits(arch, v as int);
                        t.lemma_to_int_bits(arch, x & m);
                        t.lemma_to_int_bits(arch, lit);
                        let both = ((x & m) & mask) & (lit & mask);
                        let read = x & (m & lit);
                        assert(both & mask == read & mask) by (bit_vector)
                            requires both == ((x & m) & mask) & (lit & mask), read == x & (m & lit);
                        t.lemma_to_int_mask(arch, both);
                        t.lemma_to_int_mask(arch, read);
                        assert(cty == t);
                        assert(ty == t);
                        assert(e.eval(arch, ctx, args) == t.to_int(arch, x & m));
                        assert(c.eval(arch, ctx, args) == t.to_int(arch, lit));
                        assert(self.eval(arch, ctx, args) == t.to_int(arch, both));
                        assert(self.spec_term(arch, ctx)->Some_0.2 == m & lit);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
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
    ///     <operands into pairs>   ; l op r, unless the word test applies
    ///     <word test or pairs test> -> pass/fail
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
                if !self.emit_test(b, arch, Ghost(ctx), sig, pass_at, fail_at)? {
                    let ghost tys = self.lemma_operand_types(arch, ctx);
                    proof {
                        assert(l.of_type(arch, ctx, tys.0));
                        assert(r.of_type(arch, ctx, tys.1));
                    }
                    let t1 = l.ty(arch, sig);
                    let t2 = r.ty(arch, sig);
                    let signed = t1.exec_signed() || t2.exec_signed();
                    let bias: u32 = if signed && *op != CmpOp::Eq { 0x8000_0000 } else { 0 };
                    op.emit_pairs(b, bias, pass_at, fail_at)?;
                    let ghost mid = b.rev@;
                    l.emit_operands(r, b, arch, sig, 0)?;
                    proof {
                        assert forall |data: &[u8], st: Regs|
                            #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, pass_at as nat)]
                            #![trigger Builder::lands(b.rev@, data, b.rev@.len(), st, fail_at as nat)]
                            Event::parse(data) is Some && st.wf() implies {
                            &&& self.holds(arch, ctx, data) ==>
                                Builder::lands(b.rev@, data, b.rev@.len(), st, pass_at as nat)
                            &&& !self.holds(arch, ctx, data) ==>
                                Builder::lands(b.rev@, data, b.rev@.len(), st, fail_at as nat)
                        } by {
                            let pl = l.pattern(arch, ctx, data);
                            let pr = r.pattern(arch, ctx, data);
                            self.lemma_pairs(arch, ctx, data, t1, t2);
                            let to = if self.holds(arch, ctx, data) { pass_at } else { fail_at };
                            assert(Builder::stores2(b.rev@, data, b.rev@.len(), st, mid.len(), 0, pl, pr));
                            let t = choose |t: Regs| t.wf() && t.holds(0, pl) && t.holds(1, pr)
                                && t.keeps(st, 0) && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, mid.len(), t);
                            assert(Builder::lands(mid, data, mid.len(), t, to as nat));
                            Builder::lemma_then(mid, b.rev@, data, b.rev@.len(), st, mid.len(), t, to as nat, 0);
                        }
                    }
                }
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

    /// A comparison holds as the test of its operands' pairs says, read as signed if
    /// either operand is.
    proof fn lemma_pairs(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8], t1: PrimType, t2: PrimType)
        requires
            self is Cmp,
            self.wf(arch, ctx),
            self->Cmp_1.shaped(arch, ctx, t1),
            self->Cmp_2.shaped(arch, ctx, t2),
        ensures ({
            let pl = self->Cmp_1.pattern(arch, ctx, data);
            let pr = self->Cmp_2.pattern(arch, ctx, data);
            let bias: u32 = if (t1.signed() || t2.signed()) && !(self->Cmp_0 is Eq) { 0x8000_0000 } else { 0 };
            self.holds(arch, ctx, data) <==> self->Cmp_0.wide_holds(((pl >> 32) as u32) ^ bias, pl as u32,
                ((pr >> 32) as u32) ^ bias, pr as u32)
        })
    {
        match self {
            Cond::Cmp(op, l, r) => {
                let (ty1, ty2) = self.lemma_operand_types(arch, ctx);
                l.lemma_unpat(arch, ctx, data, ty1);
                r.lemma_unpat(arch, ctx, data, ty2);
                let pl = l.pattern(arch, ctx, data);
                let pr = r.pattern(arch, ctx, data);
                let signed = t1.signed() || t2.signed();
                let bias: u32 = if signed && !(*op is Eq) { 0x8000_0000 } else { 0 };
                // Only an unsigned operand narrower than the other meets a signed one, so
                // both read alike as signed.
                let ty = if signed { PrimType::I(64) } else { PrimType::U(64) };
                ty.lemma_unpat_64(arch, pl);
                ty.lemma_unpat_64(arch, pr);
                op.lemma_wide_truth(ty, arch, pl, pr, bias);
            }
            _ => {}
        }
    }

    /// Emits the word tests of this comparison between a masked argument and a literal
    /// of the argument's width and signedness, and returns whether it applies.
    ///
    /// ```text
    ///     ld  [lo]                ; at most 32 bits
    ///     and #mask               ; mask != 0xffffffff
    ///     xor #bias               ; bias != 0
    ///     j<op> #k -> pass/fail
    ///
    ///     <two-word test> -> pass/fail    ; 64 bits
    /// ```
    fn emit_test(&self, b: &mut Builder, arch: Arch, Ghost(ctx): Ghost<Seq<PrimType>>,
        sig: &[PrimType], pass: Label, fail: Label) -> (res: Result<bool, CompileError>)
        requires
            self is Cmp,
            self.wf(arch, ctx),
            sig@ == ctx,
            0 < pass <= old(b).rev@.len(),
            0 < fail <= old(b).rev@.len(),
            pass == old(b).rev@.len() || fail == old(b).rev@.len(),
            old(b).wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res matches Ok(false) ==> final(b).rev@ == old(b).rev@,
            res matches Ok(true) ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && self.holds(arch, ctx, data) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), st, pass as nat),
            res matches Ok(true) ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf()
                && !self.holds(arch, ctx, data) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), st, fail as nat),
    {
        let (op, l, r) = match self {
            Cond::Cmp(op, l, r) => (*op, l, r),
            _ => return Ok(false),
        };
        let (i, ty, m) = match l.term(arch, sig) {
            Some(term) => term,
            None => return Ok(false),
        };
        let (c, lty) = match &**r {
            Expr::Lit(c, lty) => (*c, *lty),
            _ => return Ok(false),
        };
        let width = ty.exec_bits(arch);
        if lty.exec_bits(arch) != width || lty.exec_signed() != ty.exec_signed() {
            return Ok(false);
        }
        if width != 16 && width != 32 && width != 64 {
            return Ok(false);
        }
        let ghost tys = self.lemma_operand_types(arch, ctx);
        proof {
            l.lemma_term(arch, ctx, Seq::empty(), tys.0);
        }
        let slot = arch.arg_slot(sig, i as usize)?;

        let mm = m & ty.exec_mask(arch);
        let q = lty.lit_bits(arch, c);
        let order = ty.exec_signed() && op != CmpOp::Eq;
        let lo = Policy::OFFSET_EVENT_ARGS + 8 * slot;
        if width == 64 {
            let hi = if arch.exec_splits(sig[i as usize]) { lo + 8 } else { lo + 4 };
            let bias: u32 = if order { 0x8000_0000 } else { 0 };
            let k_hi = ((q >> 32) as u32) ^ bias;
            op.emit_wide(b, lo, hi, mm as u32, (mm >> 32) as u32, bias, q as u32, k_hi, pass, fail)?;
            proof {
                assert forall |data: &[u8]| #[trigger] Event::parse(data) is Some implies
                    (self.holds(arch, ctx, data) <==> op.wide_holds(
                        (Builder::word(data, hi) & ((mm >> 32) as u32)) ^ bias,
                        Builder::word(data, lo) & (mm as u32), k_hi, q as u32)) by {
                    let ev = Event::of(data);
                    let args = arch.interp_args(ev.args, ctx);
                    Event::lemma_image(data);
                    l.lemma_term(arch, ctx, args, tys.0);
                    let raw = args[i as int];
                    assert(raw == arch.raw(ev.args, ctx[i as int], slot as nat));
                    arch.lemma_raw_words(ev.args, ctx[i as int], slot as nat);
                    let lv = ev.args[slot as int];
                    assert((lv & 0xFFFF_FFFF) as u32 == lv as u32) by (bit_vector);
                    if arch.splits(ctx[i as int]) {
                        let hv = ev.args[slot + 1 as int];
                        assert((hv & 0xFFFF_FFFF) as u32 == hv as u32) by (bit_vector);
                        assert(Builder::word(data, hi) == hv as u32);
                    } else {
                        assert(Builder::word(data, hi) == (lv >> 32) as u32);
                    }
                    assert(Builder::word(data, lo) == raw as u32);
                    assert(Builder::word(data, hi) == (raw >> 32) as u32);
                    let p = raw & mm;
                    let mask = ty.mask(arch);
                    CmpOp::lemma_words(raw, mm);
                    ty.lemma_to_int_mask(arch, raw & m);
                    assert((raw & m) & mask == p) by (bit_vector)
                        requires p == raw & mm, mm == m & mask;
                    ty.lemma_to_int_mask(arch, p);
                    lty.lemma_same(ty, arch);
                    op.lemma_wide_truth(ty, arch, p, q, bias);
                    assert(l.eval(arch, ctx, args) == ty.to_int(arch, p));
                    assert(r.eval(arch, ctx, args) == ty.to_int(arch, q));
                    assert((Builder::word(data, hi) & ((mm >> 32) as u32)) == (p >> 32) as u32);
                    assert((Builder::word(data, lo) & (mm as u32)) == p as u32);
                    assert(self.holds(arch, ctx, data) <==> op.holds(ty.to_int(arch, p), ty.to_int(arch, q)));
                }
            }
        } else {
            let bias: u32 = if !order { 0 } else if width == 16 { 0x8000 } else { 0x8000_0000 };
            let k = (q as u32) ^ bias;
            op.emit_jump(b, Src::K(k), pass, fail)?;
            b.emit_load(lo, mm as u32, bias);
            proof {
                assert forall |data: &[u8]| #[trigger] Event::parse(data) is Some implies
                    (self.holds(arch, ctx, data) <==> op.holds(
                        ((Builder::word(data, lo) & (mm as u32)) ^ bias) as int, k as int)) by {
                    let ev = Event::of(data);
                    let args = arch.interp_args(ev.args, ctx);
                    Event::lemma_image(data);
                    l.lemma_term(arch, ctx, args, tys.0);
                    let raw = args[i as int];
                    assert(raw == arch.raw(ev.args, ctx[i as int], slot as nat));
                    assert((raw & 0xFFFF_FFFF) as u32 == raw as u32) by (bit_vector);
                    let mask = ty.mask(arch);
                    if width == 16 {
                        assert(((1u64 << 16u64) - 1) == 0xFFFF) by (bit_vector);
                    } else {
                        assert(((1u64 << 32u64) - 1) == 0xFFFF_FFFF) by (bit_vector);
                    }
                    let p = raw & mm;
                    assert((raw & m) & mask == p && p & !mask == 0
                        && (((raw as u32) & (mm as u32)) as u64) == p) by (bit_vector)
                        requires p == raw & mm, mm == m & mask, mask == 0xFFFF || mask == 0xFFFF_FFFF;
                    ty.lemma_to_int_mask(arch, raw & m);
                    ty.lemma_to_int_mask(arch, p);
                    lty.lemma_same(ty, arch);
                    op.lemma_word_truth(ty, arch, p, q, bias);
                    assert(l.eval(arch, ctx, args) == ty.to_int(arch, p));
                    assert(r.eval(arch, ctx, args) == ty.to_int(arch, q));
                    assert(Builder::word(data, lo) == raw as u32);
                    assert(((Builder::word(data, lo) & (mm as u32)) as u64) == p);
                    assert(self.holds(arch, ctx, data) <==> op.holds(ty.to_int(arch, p), ty.to_int(arch, q)));
                }
            }
        }
        Ok(true)
    }
}

} // verus!
