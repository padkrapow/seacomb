//! Compiling one rule: the test that reaches it, and the argument tests under it.

use vstd::prelude::*;
use crate::spec::{policy::*, syscall::*, cbpf::*};
use super::CompileError;
use super::builder::{Builder, Label};

verus! {

impl Arch {
    /// Whether an argument of type `ty` takes two slots.
    spec fn splits(self, ty: PrimType) -> bool {
        (self == Arch::X86 || self == Arch::Arm) && ty.bits(self) == 64
    }

    /// The slot after an argument of type `ty` read from `slot` on.
    spec fn next_slot(self, slot: nat, ty: PrimType) -> nat {
        if self.splits(ty) {
            (if self == Arch::Arm { slot + slot % 2 } else { slot }) + 2
        } else {
            slot + 1
        }
    }

    /// The arguments of a syscall with signature `sig`, read from `slot` on.
    spec fn interp_from(self, args: Seq<u64>, sig: Seq<PrimType>, slot: nat) -> Seq<int> {
        match self {
            Arch::X86 => Self::interp_args_x86(args.skip(slot as int), sig),
            Arch::Arm => Self::interp_args_arm(args, sig, slot as int),
            _ => Seq::new(sig.len(), |i: int| sig[i].cast(self, args[slot + i])),
        }
    }

    /// The bits of an argument of type `ty` that starts at `slot`.
    spec fn raw(self, args: Seq<u64>, ty: PrimType, slot: nat) -> u64 {
        if self.splits(ty) {
            (args[slot as int] & 0xFFFF_FFFFu64) | ((args[slot + 1 as int] & 0xFFFF_FFFFu64) << 32u64)
        } else {
            args[slot as int]
        }
    }

    /// Whether argument `n` of a syscall with signature `sig` starts at `slot`.
    spec fn arg_at(self, sig: Seq<PrimType>, n: nat, slot: nat) -> bool {
        forall |args: Seq<u64>| args.len() == Rule::ARG_COUNT_MAX ==>
            #[trigger] self.interp_args(args, sig)[n as int]
                == sig[n as int].cast(self, self.raw(args, sig[n as int], slot))
    }

    /// x86 interpretation produces one value for each signature argument.
    proof fn lemma_interp_x86_len(args: Seq<u64>, sig: Seq<PrimType>)
        ensures Self::interp_args_x86(args, sig).len() == sig.len()
        decreases sig.len()
    {
        if sig.len() > 0 {
            if sig[0].bits(Arch::X86) == 64 {
                Self::lemma_interp_x86_len(args.skip(2), sig.drop_first());
            } else {
                Self::lemma_interp_x86_len(args.drop_first(), sig.drop_first());
            }
        }
    }

    /// ARM interpretation produces one value for each signature argument.
    proof fn lemma_interp_arm_len(args: Seq<u64>, sig: Seq<PrimType>, slot: int)
        ensures Self::interp_args_arm(args, sig, slot).len() == sig.len()
        decreases sig.len()
    {
        if sig.len() > 0 {
            if sig[0].bits(Arch::Arm) == 64 {
                let aligned = slot + slot % 2;
                Self::lemma_interp_arm_len(args, sig.drop_first(), aligned + 2);
            } else {
                Self::lemma_interp_arm_len(args, sig.drop_first(), slot + 1);
            }
        }
    }

    /// Reading from slot 0 is how the kernel reads the arguments.
    proof fn lemma_from_start(self, args: Seq<u64>, sig: Seq<PrimType>)
        ensures self.interp_from(args, sig, 0) =~= self.interp_args(args, sig)
    {
        assert(args.skip(0) =~= args);
    }

    /// Past the first argument read from `slot`, the rest are read from the next slot.
    proof fn lemma_from_next(self, args: Seq<u64>, sig: Seq<PrimType>, slot: nat, j: int)
        requires 0 < j < sig.len(), self.next_slot(slot, sig[0]) <= args.len()
        ensures self.interp_from(args, sig, slot)[j]
            == self.interp_from(args, sig.drop_first(), self.next_slot(slot, sig[0]))[j - 1]
    {
        let next = self.next_slot(slot, sig[0]);
        match self {
            Arch::X86 => {
                let step: int = if sig[0].bits(self) == 64 { 2 } else { 1 };
                if step == 2 {
                    assert(args.skip(slot as int).skip(2) =~= args.skip(next as int));
                } else {
                    assert(args.skip(slot as int).drop_first() =~= args.skip(next as int));
                }
                Self::lemma_interp_x86_len(args.skip(next as int), sig.drop_first());
            }
            Arch::Arm => Self::lemma_interp_arm_len(args, sig.drop_first(), next as int),
            _ => {}
        }
    }

    /// The first argument read from `slot` is its bits there, once aligned.
    proof fn lemma_from_first(self, args: Seq<u64>, sig: Seq<PrimType>, slot: nat)
        requires 0 < sig.len(), self.next_slot(slot, sig[0]) <= args.len()
        ensures self.interp_from(args, sig, slot)[0] == sig[0].cast(self, self.raw(args, sig[0],
            if self == Arch::Arm && self.splits(sig[0]) { slot + slot % 2 } else { slot }))
    {
        if self == Arch::X86 {
            assert(args.skip(slot as int)[0] == args[slot as int]);
            if self.splits(sig[0]) {
                assert(args.skip(slot as int)[1] == args[slot + 1 as int]);
            }
        }
    }

    /// The low and high words of the bits of a 64-bit argument that starts at `slot`.
    proof fn lemma_raw_words(self, args: Seq<u64>, ty: PrimType, slot: nat)
        requires ty.bits(self) == 64, slot < args.len(), self.splits(ty) ==> slot + 1 < args.len()
        ensures
            self.raw(args, ty, slot) as u32 == args[slot as int] as u32,
            (self.raw(args, ty, slot) >> 32) as u32 == if self.splits(ty) {
                args[slot + 1 as int] as u32
            } else {
                (args[slot as int] >> 32) as u32
            },
    {
        let l = args[slot as int];
        if self.splits(ty) {
            let h = args[slot + 1 as int];
            assert((((l & 0xFFFF_FFFFu64) | ((h & 0xFFFF_FFFFu64) << 32u64)) as u32) == l as u32)
                by (bit_vector);
            assert(((((l & 0xFFFF_FFFFu64) | ((h & 0xFFFF_FFFFu64) << 32u64)) >> 32u64) as u32)
                == h as u32) by (bit_vector);
        }
    }

    /// Returns the slot where argument `n` of a syscall with signature `sig` starts.
    fn arg_slot(self, sig: &[PrimType], n: usize) -> (res: Result<u32, CompileError>)
        requires n < sig@.len()
        ensures res matches Ok(slot) ==> {
            &&& slot < Rule::ARG_COUNT_MAX
            &&& self.splits(sig@[n as int]) ==> slot + 1 < Rule::ARG_COUNT_MAX
            &&& self.arg_at(sig@, n as nat, slot as nat)
        }
    {
        let mut slot: u32 = 0;
        let mut i: usize = 0;
        proof {
            assert(sig@.skip(0) =~= sig@);
            assert forall |args: Seq<u64>| args.len() == Rule::ARG_COUNT_MAX implies
                #[trigger] self.interp_args(args, sig@)[n as int]
                    == self.interp_from(args, sig@.skip(0), 0)[n as int] by {
                self.lemma_from_start(args, sig@);
            }
        }
        while i < n
            invariant
                i <= n < sig@.len(),
                slot <= Rule::ARG_COUNT_MAX,
                forall |args: Seq<u64>| args.len() == Rule::ARG_COUNT_MAX ==>
                    #[trigger] self.interp_args(args, sig@)[n as int]
                        == self.interp_from(args, sig@.skip(i as int), slot as nat)[n - i],
            decreases n - i
        {
            let ghost prev = slot;
            if self.exec_splits(sig[i]) {
                if self == Arch::Arm && !slot.is_multiple_of(2) {
                    slot += 1;
                }
                if slot > 4 {
                    return Err(CompileError::SignatureLayout);
                }
                slot += 2;
            } else {
                if slot >= Rule::ARG_COUNT_MAX {
                    return Err(CompileError::SignatureLayout);
                }
                slot += 1;
            }
            proof {
                let rest = sig@.skip(i as int);
                assert(rest.drop_first() =~= sig@.skip(i + 1));
                assert forall |args: Seq<u64>| args.len() == Rule::ARG_COUNT_MAX implies
                    #[trigger] self.interp_args(args, sig@)[n as int]
                        == self.interp_from(args, sig@.skip(i + 1), slot as nat)[n - i - 1] by {
                    self.lemma_from_next(args, rest, prev as nat, n - i);
                }
            }
            i += 1;
        }
        let ghost unaligned = slot;
        let split = self.exec_splits(sig[n]);
        if self == Arch::Arm && split && !slot.is_multiple_of(2) {
            slot += 1;
        }
        if slot >= Rule::ARG_COUNT_MAX || split && slot > 4 {
            return Err(CompileError::SignatureLayout);
        }
        proof {
            let rest = sig@.skip(n as int);
            assert forall |args: Seq<u64>| args.len() == Rule::ARG_COUNT_MAX implies
                #[trigger] self.interp_args(args, sig@)[n as int]
                    == sig@[n as int].cast(self, self.raw(args, sig@[n as int], slot as nat)) by {
                self.lemma_from_first(args, rest, unaligned as nat);
            }
        }
        Ok(slot)
    }

    /// Executable version of [`Arch::splits`].
    fn exec_splits(self, ty: PrimType) -> (res: bool)
        ensures res == self.splits(ty)
    {
        (self == Arch::X86 || self == Arch::Arm) && ty.exec_bits(self) == 64
    }
}

impl Rule {
    /// Number of argument slots in `seccomp_data`.
    pub const ARG_COUNT_MAX: u32 = 6;
}

impl PrimType {
    /// Casting preserves the argument's low bits modulo its type width.
    proof fn lemma_cast_bits(self, arch: Arch, x: u64)
        ensures
            (self.cast(arch, x) % (self.mask(arch) + 1)) as u64
                == x & self.mask(arch),
    {
        let mask = self.mask(arch);
        let pattern = x & mask;
        assert((x & mask) <= mask) by (bit_vector);
        let modulus: int = mask as int + 1;
        vstd::arithmetic::div_mod::lemma_small_mod(pattern as nat, modulus as nat);
        if self.signed() && pattern > mask >> 1u64 {
            vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(
                pattern as int, modulus);
            assert((pattern as int - modulus) % modulus == pattern as int);
        }
    }

    /// Equal casts have equal bit patterns, and equal bit patterns have equal casts.
    proof fn lemma_cast_eq(self, arch: Arch, x: u64, y: u64)
        ensures
            (self.cast(arch, x) == self.cast(arch, y))
                <==> (x & self.mask(arch) == y & self.mask(arch)),
    {
        self.lemma_cast_bits(arch, x);
        self.lemma_cast_bits(arch, y);
    }

    /// Flipping the sign bit turns signed narrow ordering into unsigned ordering.
    proof fn lemma_signed_bias(self, arch: Arch, x: u64, y: u64)
        requires
            self.signed(),
            self.bits(arch) == 16 || self.bits(arch) == 32,
        ensures
            (self.cast(arch, x) < self.cast(arch, y)) <==> {
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
                assert(self.cast(arch, x) == px as int - (mask as int + 1));
                assert(self.cast(arch, y) == py as int - (mask as int + 1));
            }
        } else if py > half {
            assert(self.cast(arch, x) == px as int);
            assert(self.cast(arch, y) == py as int - (mask as int + 1));
        }
    }

    /// Flipping bit 63 turns signed 64-bit ordering into unsigned ordering.
    proof fn lemma_signed_bias_64(self, arch: Arch, x: u64, y: u64)
        requires self.signed(), self.bits(arch) == 64
        ensures
            (self.cast(arch, x) < self.cast(arch, y))
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
                assert(self.cast(arch, x) == x as int - (mask as int + 1));
                assert(self.cast(arch, y) == y as int - (mask as int + 1));
            }
        } else if y > half {
            assert(self.cast(arch, x) == x as int);
            assert(self.cast(arch, y) == y as int - (mask as int + 1));
        }
    }

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
}

impl Compare {
    /// Whether word `x` passes this comparison against `k`, with a `MaskedEq` word already masked.
    spec fn holds(self, x: u32, k: u32) -> bool {
        match self {
            Compare::Eq | Compare::MaskedEq => x == k,
            Compare::Ne => x != k,
            Compare::Lt => x < k,
            Compare::Le => x <= k,
            Compare::Ge => x >= k,
            Compare::Gt => x > k,
        }
    }

    /// Whether this is one of the four ordering comparisons.
    spec fn orders(self) -> bool {
        self is Lt || self is Le || self is Gt || self is Ge
    }

    /// The jump, as [`Builder::emit_jump`] takes it, that leaves a failing one-word test.
    fn fail_jump(self) -> (res: (JmpOp, bool))
        ensures forall |x: u32, k: u32| #[trigger] res.0.eval(x, k) == res.1 <==> !self.holds(x, k)
    {
        match self {
            Compare::Eq | Compare::MaskedEq => (JmpOp::Eq, false),
            Compare::Ne => (JmpOp::Eq, true),
            Compare::Lt => (JmpOp::Ge, true),
            Compare::Le => (JmpOp::Gt, true),
            Compare::Ge => (JmpOp::Ge, false),
            Compare::Gt => (JmpOp::Gt, false),
        }
    }

    /// Emits a test of the word at `at` that leaves for `fail` unless it passes.
    ///
    /// ```text
    ///     ld  [at]
    ///     and #mask               ; mask != 0xffffffff
    ///     xor #bias               ; bias != 0
    ///     j!<op> #k -> fail
    /// ```
    fn emit_test(self, b: &mut Builder, at: u32, mask: u32, bias: u32, k: u32, fail: Label)
        -> (res: Result<(), CompileError>)
        requires at % 4 == 0, 0 < fail <= b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| at + 4 <= data@.len()
                && self.holds((Builder::word(data, at) & mask) ^ bias, k) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), a,
                    old(b).rev@.len()),
            res is Ok ==> forall |data: &[u8], a: u32| at + 4 <= data@.len()
                && !self.holds((Builder::word(data, at) & mask) ^ bias, k) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), a,
                    fail as nat),
    {
        let ghost pass = b.rev@;
        let (jmp, expect) = self.fail_jump();
        b.emit_jump(jmp, Src::K(k), expect, fail)?;
        b.emit_load(at, mask, bias);
        proof {
            assert forall |data: &[u8], x: u32|
                #[trigger] Builder::lands(pass, data, pass.len(), x, pass.len()) by {
                assert(Builder::goes_to(pass, data, pass.len(), x, pass.len(), x));
            }
        }
        Ok(())
    }
}

impl ArgCmp {
    /// Evaluates this comparison on a typed argument bit pattern.
    spec fn typed_test(self, arch: Arch, ty: PrimType, value: u64) -> bool {
        let x = ty.cast(arch, value);
        let c = ty.cast(arch, self.a);
        match self.op {
            Compare::Eq => x == c,
            Compare::Ne => x != c,
            Compare::Lt => x < c,
            Compare::Le => x <= c,
            Compare::Ge => x >= c,
            Compare::Gt => x > c,
            Compare::MaskedEq => (x % (ty.mask(arch) + 1)) as u64 & self.a == self.b,
        }
    }

    /// Whether the two-word test passes on the high and low words as it loads them.
    spec fn wide_holds(self, high: u32, low: u32, k_hi: u32, k_lo: u32) -> bool {
        if high == k_hi {
            self.op.holds(low, k_lo)
        } else if high > k_hi && self.op.orders() {
            self.op is Gt || self.op is Ge
        } else {
            self.op is Ne || self.op is Lt || self.op is Le
        }
    }

    /// Typed comparison of a 64-bit argument agrees with the two-word test.
    #[allow(clippy::too_many_arguments)]
    proof fn lemma_wide_truth(self, arch: Arch, syscall: Syscall, x: u64,
        mask_hi: u32, mask_lo: u32, bias: u32, k_hi: u32, k_lo: u32)
        requires
            self.wf(arch, syscall),
            syscall.spec_signature(arch)[self.arg as int].bits(arch) == 64,
            bias == if syscall.spec_signature(arch)[self.arg as int].signed() && self.op.orders() {
                0x8000_0000u32 } else { 0 },
            mask_hi == if self.op is MaskedEq { (self.a >> 32) as u32 } else { u32::MAX },
            mask_lo == if self.op is MaskedEq { self.a as u32 } else { u32::MAX },
            k_hi == if self.op is MaskedEq { (self.b >> 32) as u32 }
                else { ((self.a >> 32) as u32) ^ bias },
            k_lo == if self.op is MaskedEq { self.b as u32 } else { self.a as u32 },
        ensures
            self.typed_test(arch, syscall.spec_signature(arch)[self.arg as int], x)
                <==> self.wide_holds((((x >> 32) as u32) & mask_hi) ^ bias,
                    (x as u32) & mask_lo, k_hi, k_lo),
    {
        let ty = syscall.spec_signature(arch)[self.arg as int];
        let a = self.a;
        let high = (x >> 32) as u32;
        let low = x as u32;
        assert(ty.mask(arch) == u64::MAX);
        assert((x & u64::MAX) == x) by (bit_vector);
        assert((a & u64::MAX) == a) by (bit_vector);
        assert((high & u32::MAX) ^ 0u32 == high) by (bit_vector);
        assert(((a >> 32) as u32) ^ 0u32 == (a >> 32) as u32) by (bit_vector);
        assert((low & u32::MAX) == low) by (bit_vector);
        if self.op is Eq || self.op is Ne {
            ty.lemma_cast_eq(arch, x, a);
            Self::lemma_words(x, a);
        } else if self.op is MaskedEq {
            ty.lemma_cast_bits(arch, x);
            Self::lemma_words(x, a);
            Self::lemma_words(x & a, self.b);
            assert((high & mask_hi) ^ 0u32 == high & mask_hi) by (bit_vector);
        } else if ty.signed() {
            ty.lemma_signed_bias_64(arch, x, a);
            ty.lemma_signed_bias_64(arch, a, x);
            let sign = 0x8000_0000_0000_0000u64;
            Self::lemma_words(x ^ sign, a ^ sign);
            assert((((x ^ sign) >> 32) as u32) == ((((x >> 32) as u32) & u32::MAX) ^ 0x8000_0000u32))
                by (bit_vector) requires sign == 0x8000_0000_0000_0000u64;
            assert((((a ^ sign) >> 32) as u32) == (((a >> 32) as u32) ^ 0x8000_0000u32))
                by (bit_vector) requires sign == 0x8000_0000_0000_0000u64;
            assert(((x ^ sign) as u32) == (x as u32)) by (bit_vector)
                requires sign == 0x8000_0000_0000_0000u64;
            assert(((a ^ sign) as u32) == (a as u32)) by (bit_vector)
                requires sign == 0x8000_0000_0000_0000u64;
        } else {
            Self::lemma_words(x, a);
            assert(ty.cast(arch, x) == x as int);
            assert(ty.cast(arch, a) == a as int);
        }
    }

    /// Typed comparison of an argument that fits in one word agrees with the one-word test.
    #[allow(clippy::too_many_arguments)]
    proof fn lemma_word_truth(self, arch: Arch, syscall: Syscall, x: u64,
        mask: u32, bias: u32, k: u32)
        requires
            self.wf(arch, syscall),
            ({
                let ty = syscall.spec_signature(arch)[self.arg as int];
                let width = ty.bits(arch);
                &&& width == 16 || width == 32
                &&& mask == if self.op is MaskedEq { self.a as u32 }
                    else if width == 16 { 0xFFFFu32 } else { u32::MAX }
                &&& bias == if ty.signed() && self.op.orders() {
                    if width == 16 { 0x8000u32 } else { 0x8000_0000u32 }
                } else { 0 }
                &&& k == if self.op is MaskedEq { self.b as u32 }
                    else { ((self.a as u32) & mask) ^ bias }
            }),
        ensures
            self.typed_test(arch, syscall.spec_signature(arch)[self.arg as int], x)
                <==> self.op.holds(((x as u32) & mask) ^ bias, k),
    {
        let ty = syscall.spec_signature(arch)[self.arg as int];
        let a = self.a;
        let b = self.b;
        let type_mask = ty.mask(arch);
        if ty.bits(arch) == 16 {
            assert(((1u64 << 16u64) - 1) == 0xFFFF) by (bit_vector);
        } else {
            assert(((1u64 << 32u64) - 1) == 0xFFFF_FFFF) by (bit_vector);
        }
        if self.op is MaskedEq {
            ty.lemma_cast_bits(arch, x);
            assert(((x & type_mask) & a == b) <==> ((((x as u32) & (a as u32)) ^ 0u32) == (b as u32)))
                by (bit_vector)
                requires a & !type_mask == 0, b & !a == 0,
                    type_mask == 0xFFFF || type_mask == 0xFFFF_FFFF;
        } else {
            let narrow = mask;
            assert(type_mask == narrow as u64);
            assert(((x & (narrow as u64)) as u32) == ((x as u32) & narrow)) by (bit_vector);
            assert(((a & (narrow as u64)) as u32) == ((a as u32) & narrow)) by (bit_vector);
            if self.op is Eq || self.op is Ne {
                ty.lemma_cast_eq(arch, x, a);
                assert(bias == 0);
                assert((((x as u32) & narrow) ^ 0u32) == ((x as u32) & narrow)) by (bit_vector);
                assert((((a as u32) & narrow) ^ 0u32) == ((a as u32) & narrow)) by (bit_vector);
                assert((x & type_mask == a & type_mask)
                    <==> (((x as u32) & narrow) == ((a as u32) & narrow))) by (bit_vector)
                    requires type_mask == narrow as u64;
            } else if ty.signed() {
                ty.lemma_signed_bias(arch, x, a);
                ty.lemma_signed_bias(arch, a, x);
                if ty.bits(arch) == 16 {
                    assert((type_mask >> 1u64) == 0x7FFF) by (bit_vector)
                        requires type_mask == 0xFFFF;
                } else {
                    assert((type_mask >> 1u64) == 0x7FFF_FFFF) by (bit_vector)
                        requires type_mask == 0xFFFF_FFFF;
                }
                assert(((type_mask >> 1u64) + 1) as u64 == bias as u64);
                assert((((x & (narrow as u64)) ^ (bias as u64)) as u32)
                    == (((x as u32) & narrow) ^ bias)) by (bit_vector);
                assert((((a & (narrow as u64)) ^ (bias as u64)) as u32)
                    == (((a as u32) & narrow) ^ bias)) by (bit_vector);
            } else {
                assert(bias == 0);
                assert(ty.cast(arch, x) == (x & type_mask) as int);
                assert(ty.cast(arch, a) == (a & type_mask) as int);
                assert((x & (narrow as u64)) == ((((x as u32) & narrow) ^ 0u32) as u64)) by (bit_vector);
                assert((a & (narrow as u64)) == ((((a as u32) & narrow) ^ 0u32) as u64)) by (bit_vector);
            }
        }
    }

    /// Emits a typed argument comparison using the syscall's physical argument slots.
    fn emit(&self, b: &mut Builder, arch: Arch, Ghost(syscall): Ghost<Syscall>,
        sig: &[PrimType], fail: Label) -> (res: Result<(), CompileError>)
        requires
            self.wf(arch, syscall),
            sig@ =~= syscall.spec_signature(arch),
            0 < fail <= b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.eval(arch, syscall, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, old(b).rev@.len()),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.eval(arch, syscall, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, fail as nat),
    {
        let slot = arch.arg_slot(sig, self.arg as usize)?;
        let ty = sig[self.arg as usize];
        let width = ty.exec_bits(arch);
        if width == 64 {
            return self.emit_wide(b, arch, Ghost(syscall), ty, slot, fail);
        }
        if width != 16 && width != 32 {
            return Err(CompileError::UnsupportedArgWidth(width));
        }

        // An argument that fits in one word:
        //
        //      ld  [lo]
        //      and #0xffff             ; 16-bit, not MaskedEq
        //      and #a                  ; MaskedEq, unless all ones
        //      xor #bias               ; signed ordering
        //      j!<op> #k -> fail
        let lo = Policy::OFFSET_EVENT_ARGS + 8 * slot;
        let masked = self.op == Compare::MaskedEq;
        let order = self.op == Compare::Lt || self.op == Compare::Le
            || self.op == Compare::Gt || self.op == Compare::Ge;
        let mask: u32 = if masked { self.a as u32 } else if width == 16 { 0xFFFF } else { u32::MAX };
        let bias: u32 = if ty.exec_signed() && order {
            if width == 16 { 0x8000 } else { 0x8000_0000 }
        } else { 0 };
        let k = if masked { self.b as u32 } else { (self.a as u32 & mask) ^ bias };
        self.op.emit_test(b, lo, mask, bias, k, fail)?;
        proof {
            assert forall |data: &[u8]| #[trigger] Event::parse(data) is Some implies
                (self.eval(arch, syscall, Event::of(data).args)
                    <==> self.op.holds((Builder::word(data, lo) & mask) ^ bias, k)) by {
                let args = Event::of(data).args;
                Event::lemma_image(data);
                let x = args[slot as int];
                assert(arch.interp_args(args, sig@)[self.arg as int]
                    == ty.cast(arch, arch.raw(args, ty, slot as nat)));
                self.lemma_word_truth(arch, syscall, x, mask, bias, k);
                assert((x & 0xFFFF_FFFF) as u32 == x as u32) by (bit_vector);
            }
        }
        Ok(())
    }

    /// Emits a two-word comparison of a 64-bit argument.
    ///
    /// ```text
    ///     ld  [hi]
    ///     and #a_hi               ; MaskedEq, unless all ones
    ///     xor #0x80000000         ; signed ordering
    ///     jgt #k_hi -> gt         ; ordering
    ///     jne #k_hi -> neq
    ///     ld  [lo]
    ///     and #a_lo               ; MaskedEq, unless all ones
    ///     j!<op> #k_lo -> fail
    /// ```
    fn emit_wide(&self, b: &mut Builder, arch: Arch, Ghost(syscall): Ghost<Syscall>,
        ty: PrimType, slot: u32, fail: Label) -> (res: Result<(), CompileError>)
        requires
            self.wf(arch, syscall),
            ty == syscall.spec_signature(arch)[self.arg as int],
            ty.bits(arch) == 64,
            arch.arg_at(syscall.spec_signature(arch), self.arg as nat, slot as nat),
            slot < Rule::ARG_COUNT_MAX,
            arch.splits(ty) ==> slot + 1 < Rule::ARG_COUNT_MAX,
            0 < fail <= b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.eval(arch, syscall, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, old(b).rev@.len()),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.eval(arch, syscall, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, fail as nat),
    {
        let pass = b.label();
        let lo = Policy::OFFSET_EVENT_ARGS + 8 * slot;
        let hi = if arch.exec_splits(ty) { lo + 8 } else { lo + 4 };
        let masked = self.op == Compare::MaskedEq;
        let order = self.op == Compare::Lt || self.op == Compare::Le
            || self.op == Compare::Gt || self.op == Compare::Ge;
        let below = self.op == Compare::Ne || self.op == Compare::Lt || self.op == Compare::Le;
        let bias: u32 = if ty.exec_signed() && order { 0x8000_0000 } else { 0 };
        let a_hi = (self.a >> 32) as u32;
        let (mask_lo, k_lo) = if masked { (self.a as u32, self.b as u32) } else { (u32::MAX, self.a as u32) };
        let (mask_hi, k_hi) = if masked { (a_hi, (self.b >> 32) as u32) } else { (u32::MAX, a_hi ^ bias) };
        self.op.emit_test(b, lo, mask_lo, 0, k_lo, fail)?;
        let ghost r_lo = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(k_hi), false, if below { pass } else { fail })?;
        let ghost r_ne = b.rev@;
        if order {
            b.emit_jump(JmpOp::Gt, Src::K(k_hi), true, if below { fail } else { pass })?;
        }
        let ghost r_gt = b.rev@;
        b.emit_load(hi, mask_hi, bias);
        proof {
            assert forall |data: &[u8]| #[trigger] Event::parse(data) is Some implies {
                let hm = (Builder::word(data, hi) & mask_hi) ^ bias;
                &&& self.eval(arch, syscall, Event::of(data).args) ==>
                    Builder::lands(r_gt, data, r_gt.len(), hm, pass as nat)
                &&& !self.eval(arch, syscall, Event::of(data).args) ==>
                    Builder::lands(r_gt, data, r_gt.len(), hm, fail as nat)
            } by {
                let args = Event::of(data).args;
                Event::lemma_image(data);
                let x = arch.raw(args, ty, slot as nat);
                assert(arch.interp_args(args, syscall.spec_signature(arch))[self.arg as int]
                    == ty.cast(arch, x));
                arch.lemma_raw_words(args, ty, slot as nat);
                let l = Builder::word(data, lo);
                let h = Builder::word(data, hi);
                let lv = args[slot as int];
                assert((lv & 0xFFFF_FFFF) as u32 == lv as u32) by (bit_vector);
                if arch.splits(ty) {
                    let hv = args[slot + 1 as int];
                    assert((hv & 0xFFFF_FFFF) as u32 == hv as u32) by (bit_vector);
                    assert(h == hv as u32);
                } else {
                    assert(h == (lv >> 32) as u32);
                }
                assert(l == x as u32);
                assert(h == (x >> 32) as u32);
                self.lemma_wide_truth(arch, syscall, x, mask_hi, mask_lo, bias, k_hi, k_lo);
                let hm = (h & mask_hi) ^ bias;
                assert(((l & mask_lo) ^ 0u32) == l & mask_lo) by (bit_vector);
                let to = if self.eval(arch, syscall, args) { pass as nat } else { fail as nat };
                if hm == k_hi {
                    assert(Builder::lands(r_lo, data, r_lo.len(), hm, to));
                }
                if !(order && hm > k_hi) {
                    assert(Builder::lands(r_ne, data, r_ne.len(), hm, to));
                }
                assert(Builder::lands(r_gt, data, r_gt.len(), hm, to));
            }
        }
        Ok(())
    }
}

impl Rule {
    /// Emits the test that reaches this rule at syscall number `nr`, and the rule's
    /// body under it.
    ///
    /// Forward layout, entered with `A` holding `seccomp_data.nr`:
    ///
    /// ```text
    ///     jne #nr -> end
    ///     <body>
    ///     ld  [nr]            ; hands A back to the test behind this one
    /// end:
    /// ```
    fn emit(&self, b: &mut Builder, arch: Arch, nr: u32) -> (res: Result<(), CompileError>)
        requires
            forall |i: int| #![trigger self.conds@[i]]
                0 <= i < self.conds@.len() ==> self.conds@[i].wf(arch, self.syscall),
            0 < b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && self.matches_at(arch, nr, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && !self.matches_at(arch, nr, Event::of(data)) ==>
                #[trigger] Builder::goes_to(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, old(b).rev@.len(), Event::of(data).nr as u32),
    {
        let end = b.label();
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_NR));
        proof { Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_NR); }
        let ghost r_nr = b.rev@;
        self.emit_body(b, arch, nr)?;
        let ghost r_body = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(nr), false, end)?;
        proof {
            assert forall |data: &[u8]|
                #![trigger Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32, self.action.to_ret())]
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    end as nat, Event::of(data).nr as u32)]
                Event::parse(data) is Some implies
                if self.matches_at(arch, nr, Event::of(data)) {
                    Builder::returns(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32, self.action.to_ret())
                } else {
                    Builder::goes_to(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                        end as nat, Event::of(data).nr as u32)
                } by {
                let ev = Event::of(data);
                Event::lemma_image(data);
                if ev.nr as u32 == nr {
                    assert(Builder::goes_to(b.rev@, data, b.rev@.len(), nr, r_body.len(), nr));
                    if self.body_holds(arch, nr, ev) {
                        assert(Builder::returns(r_body, data, r_body.len(), nr, self.action.to_ret()));
                        Builder::lemma_then(r_body, b.rev@, data, b.rev@.len(), nr, r_body.len(), nr,
                            0, self.action.to_ret());
                    } else {
                        assert(Builder::lands(r_body, data, r_body.len(), nr, r_nr.len()));
                        assert(Builder::goes_to_all(r_nr, data, r_nr.len(), end as nat, nr));
                        Builder::lemma_then_any(r_nr, r_body, data, r_body.len(), nr, r_nr.len(),
                            end as nat, nr);
                        Builder::lemma_then(r_body, b.rev@, data, b.rev@.len(), nr, r_body.len(), nr,
                            end as nat, nr);
                    }
                }
            }
        }
        Ok(())
    }

    /// Emits whatever this rule tests beyond the syscall number, then its action.
    ///
    /// Forward layout, with `end` just past the body:
    ///
    /// ```text
    ///     <test of one argument> -> end
    ///     ...
    ///     ret #action
    /// end:
    /// ```
    /// Reached through a multiplexer, the rule's own syscall is what the multiplexer
    /// selects on, and that selector is the only test:
    /// ```text
    ///     ld  [arg 0]
    ///     and #0xffff         ; ipc only
    ///     jne #selector -> end
    ///     ret #action
    /// end:
    /// ```
    fn emit_body(&self, b: &mut Builder, arch: Arch, nr: u32) -> (res: Result<(), CompileError>)
        requires
            forall |i: int| #![trigger self.conds@[i]]
                0 <= i < self.conds@.len() ==> self.conds@[i].wf(arch, self.syscall),
            0 < b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.body_holds(arch, nr, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    a, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.body_holds(arch, nr, Event::of(data)) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, old(b).rev@.len()),
    {
        let end = b.label();
        let ghost base = b.rev@;
        b.emit(Instr::Ret(RetVal::K(self.action.exec_to_ret())));
        let ghost r_ret = b.rev@;
        proof {
            Builder::lemma_ret(r_ret, self.action.to_ret());
            assert forall |data: &[u8], a: u32| #[trigger] Builder::returns(r_ret, data,
                r_ret.len(), a, self.action.to_ret()) by {
                assert(Builder::returns_all(r_ret, data, r_ret.len(), self.action.to_ret()));
            }
        }

        if let Some(arg) = self.mux_arg(arch) {
            if self.mux_nr(arch) == Some(nr) {
                let mask: u32 = if self.syscall.ipc_arg().is_some() { 0xFFFF } else { u32::MAX };
                b.emit_jump(JmpOp::Eq, Src::K(arg), false, end)?;
                let ghost r_sel = b.rev@;
                b.emit_load(Policy::OFFSET_EVENT_ARGS, mask, 0);
                proof {
                    assert forall |data: &[u8], a: u32|
                        #![trigger Builder::returns(b.rev@, data, b.rev@.len(), a, self.action.to_ret())]
                        #![trigger Builder::lands(b.rev@, data, b.rev@.len(), a, base.len())]
                        Event::parse(data) is Some implies
                        if self.body_holds(arch, nr, Event::of(data)) {
                            Builder::returns(b.rev@, data, b.rev@.len(), a, self.action.to_ret())
                        } else {
                            Builder::lands(b.rev@, data, b.rev@.len(), a, base.len())
                        } by {
                        let arg0 = Event::of(data).args[0];
                        let w = Builder::word(data, Policy::OFFSET_EVENT_ARGS);
                        Event::lemma_image(data);
                        assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * 0) as u32)
                            == (arg0 & 0xFFFF_FFFF) as u32);
                        Self::lemma_ipc_selector(arg0);
                        assert((w & u32::MAX) ^ 0u32 == w) by (bit_vector);
                        assert((w & 0xFFFF) ^ 0u32 == w & 0xFFFF) by (bit_vector);
                        let sel = (w & mask) ^ 0;
                        assert(self.body_holds(arch, nr, Event::of(data)) <==> sel == arg);
                        if self.body_holds(arch, nr, Event::of(data)) {
                            assert(Builder::goes_to(r_ret, data, r_ret.len(), sel, r_ret.len(), sel));
                            assert(Builder::lands(r_sel, data, r_sel.len(), sel, r_ret.len()));
                            assert(Builder::lands(b.rev@, data, b.rev@.len(), a, r_ret.len()));
                            Builder::lemma_then_any(r_ret, b.rev@, data, b.rev@.len(), a,
                                r_ret.len(), 0, self.action.to_ret());
                        }
                    }
                }
                return Ok(());
            }
        }

        if self.conds.is_empty() {
            return Ok(());
        }
        let sig = self.syscall.signature(arch);
        let mut i = self.conds.len();
        while i > 0
            invariant
                i <= self.conds@.len(),
                sig@ =~= self.syscall.spec_signature(arch),
                forall |j: int| #![trigger self.conds@[j]]
                    0 <= j < self.conds@.len() ==> self.conds@[j].wf(arch, self.syscall),
                0 < end == old(b).rev@.len(),
                b.wf(),
                Builder::extends(old(b).rev@, b.rev@),
                forall |data: &[u8], a: u32| Event::parse(data) is Some
                    && self.conds_hold(arch, Event::of(data), i as int) ==>
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), a, self.action.to_ret()),
                forall |data: &[u8], a: u32| Event::parse(data) is Some
                    && !self.conds_hold(arch, Event::of(data), i as int) ==>
                    #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), a, end as nat),
            decreases i
        {
            let ghost r_prev = b.rev@;
            i -= 1;
            self.conds[i].emit(b, arch, Ghost(self.syscall), sig, end)?;
            let ghost r_cond = b.rev@;
            proof {
                assert forall |data: &[u8], a: u32|
                    Event::parse(data) is Some
                    && self.conds_hold(arch, Event::of(data), i as int)
                    implies #[trigger] Builder::returns(r_cond, data, r_cond.len(), a,
                        self.action.to_ret()) by {
                    let ev = Event::of(data);
                    assert(self.conds@[i as int].eval(arch, self.syscall, ev.args));
                    assert(self.conds_hold(arch, ev, i + 1));
                    assert(Builder::lands(r_cond, data, r_cond.len(), a, r_prev.len()));
                    assert(Builder::returns_all(r_prev, data, r_prev.len(), self.action.to_ret()));
                    Builder::lemma_then_any(r_prev, r_cond, data, r_cond.len(), a, r_prev.len(),
                        0, self.action.to_ret());
                }
                assert forall |data: &[u8], a: u32|
                    Event::parse(data) is Some
                    && !self.conds_hold(arch, Event::of(data), i as int)
                    implies #[trigger] Builder::lands(r_cond, data, r_cond.len(), a,
                        end as nat) by {
                    let ev = Event::of(data);
                    if self.conds@[i as int].eval(arch, self.syscall, ev.args) {
                        assert(!self.conds_hold(arch, ev, i + 1));
                        assert(Builder::lands(r_cond, data, r_cond.len(), a, r_prev.len()));
                        let m = choose |m: u32| Builder::goes_to(r_cond, data, r_cond.len(), a,
                            r_prev.len(), m);
                        assert(Builder::lands(r_prev, data, r_prev.len(), m, end as nat));
                        Builder::lemma_then(r_prev, r_cond, data, r_cond.len(), a, r_prev.len(),
                            m, end as nat, a);
                    }
                }
            }
        }
        Ok(())
    }

    /// The call number the x86 multiplexer selects this rule's syscall on, if one
    /// reaches it.
    pub(super) open spec fn spec_mux_arg(&self, arch: Arch) -> Option<u32> {
        if arch != Arch::X86 || self.no_mux {
            None
        } else {
            match self.syscall.to_socketcall_arg() {
                Some(arg) => Some(arg as u32),
                None => match self.syscall.to_ipc_arg() {
                    Some(arg) => Some(arg as u32),
                    None => None,
                },
            }
        }
    }

    /// Executable version of [`Rule::spec_mux_arg`].
    #[verifier::when_used_as_spec(spec_mux_arg)]
    fn mux_arg(&self, arch: Arch) -> (res: Option<u32>)
        ensures res == self.spec_mux_arg(arch)
    {
        if arch != Arch::X86 || self.no_mux {
            return None;
        }
        match self.syscall.socketcall_arg() {
            Some(arg) => Some(arg as u32),
            None => self.syscall.ipc_arg().map(|arg: u64| -> (res: u32)
                ensures res == arg as u32
            { arg as u32 }),
        }
    }

    /// The number of the x86 multiplexer that also reaches this rule, if one does.
    pub(super) open spec fn spec_mux_nr(&self, arch: Arch) -> Option<u32> {
        if arch != Arch::X86 || self.no_mux
            || self.syscall.to_socketcall_arg() is None && self.syscall.to_ipc_arg() is None {
            None
        } else {
            let mux = if self.syscall.to_socketcall_arg() is Some {
                Syscall::Socketcall
            } else {
                Syscall::Ipc
            };
            match mux.spec_nr(arch) {
                Some(nr) => Some(nr as u32),
                None => None,
            }
        }
    }

    /// Executable version of [`Rule::spec_mux_nr`].
    #[verifier::when_used_as_spec(spec_mux_nr)]
    pub(super) fn mux_nr(&self, arch: Arch) -> (res: Option<u32>)
        ensures res == self.spec_mux_nr(arch)
    {
        if arch != Arch::X86 || self.no_mux {
            return None;
        }
        let mux = if self.syscall.socketcall_arg().is_some() {
            Syscall::Socketcall
        } else if self.syscall.ipc_arg().is_some() {
            Syscall::Ipc
        } else {
            return None;
        };
        mux.nr(arch).map(|nr: i32| -> (res: u32)
            ensures res == nr as u32
        { nr as u32 })
    }
}

impl Rule {
    /// Emits the direct and multiplexed syscall tests for this rule.
    ///
    /// ```text
    ///     <direct syscall test and argument conditions>
    ///     <multiplexer test and call-number condition>
    /// ```
    pub(super) fn emit_tests(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires
            forall |i: int| #![trigger self.conds@[i]]
                0 <= i < self.conds@.len() ==> self.conds@[i].wf(arch, self.syscall),
            0 < b.rev@.len(), b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && self.eval(arch, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && !self.eval(arch, Event::of(data)) ==>
                #[trigger] Builder::goes_to(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, old(b).rev@.len(), Event::of(data).nr as u32),
    {
        let ghost prev = b.rev@;
        if let Some(nr) = self.mux_nr(arch) {
            self.emit(b, arch, nr)?;
        }
        let ghost mux = b.rev@;
        if let Some(nr) = self.syscall.bpf_nr(arch) {
            self.emit(b, arch, nr)?;
        }
        proof {
            assert forall |data: &[u8]|
                #![trigger Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32, self.action.to_ret())]
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    prev.len(), Event::of(data).nr as u32)]
                Event::parse(data) is Some implies
                if self.eval(arch, Event::of(data)) {
                    Builder::returns(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32, self.action.to_ret())
                } else {
                    Builder::goes_to(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32, prev.len(), Event::of(data).nr as u32)
                } by {
                let ev = Event::of(data);
                let nr = ev.nr as u32;
                Event::lemma_image(data);
                self.lemma_matches(arch, ev);
                let own = match self.syscall.spec_bpf_nr(arch) {
                    Some(n) => self.matches_at(arch, n, ev),
                    None => false,
                };
                if !own {
                    assert(Builder::goes_to(b.rev@, data, b.rev@.len(), nr, mux.len(), nr));
                    if self.eval(arch, ev) {
                        assert(Builder::returns(mux, data, mux.len(), nr, self.action.to_ret()));
                        Builder::lemma_then(mux, b.rev@, data, b.rev@.len(), nr, mux.len(), nr,
                            0, self.action.to_ret());
                    } else {
                        assert(Builder::goes_to(mux, data, mux.len(), nr, prev.len(), nr));
                        Builder::lemma_then(mux, b.rev@, data, b.rev@.len(), nr, mux.len(), nr,
                            prev.len(), nr);
                    }
                }
            }
        }
        Ok(())
    }
}

} // verus!
