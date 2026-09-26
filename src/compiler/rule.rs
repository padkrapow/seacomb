//! Compiling one rule: the test that reaches it, and the argument tests under it.

use vstd::prelude::*;
use crate::spec::{policy::*, syscall::*, cbpf::*};
use super::CompileError;
use super::builder::{Builder, Label};

verus! {

impl Arch {
    /// The slot after consuming one virtual argument.
    spec fn next_slot(self, slot: nat, ty: PrimType) -> nat {
        if (self == Arch::X86 || self == Arch::Arm) && ty.bits(self) == 64 {
            (if self == Arch::Arm { slot + slot % 2 } else { slot }) + 2
        } else {
            slot + 1
        }
    }

    /// The first free physical slot after `n` virtual arguments from `slot`.
    spec fn slot_from(self, sig: Seq<PrimType>, n: nat, slot: nat) -> nat
        decreases n
    {
        if n == 0 { slot }
        else { self.slot_from(sig.drop_first(), (n - 1) as nat,
            self.next_slot(slot, sig[0])) }
    }

    /// The first free physical slot after `n` virtual arguments.
    spec fn slot_before(self, sig: Seq<PrimType>, n: nat) -> nat {
        self.slot_from(sig, n, 0)
    }

    /// Consuming argument `n` advances the first free physical slot.
    proof fn lemma_slot_next(self, sig: Seq<PrimType>, n: nat, slot: nat)
        requires n < sig.len()
        ensures self.slot_from(sig, n + 1, slot)
            == self.next_slot(self.slot_from(sig, n, slot), sig[n as int])
        decreases n
    {
        reveal_with_fuel(Arch::slot_from, 2);
        if n > 0 {
            let tail = sig.drop_first();
            let next = self.next_slot(slot, sig[0]);
            self.lemma_slot_next(tail, (n - 1) as nat, next);
            assert(tail[(n - 1) as int] == sig[n as int]);
            assert(self.slot_from(sig, n + 1, slot)
                == self.slot_from(tail, n, next));
            assert(self.slot_from(sig, n, slot)
                == self.slot_from(tail, (n - 1) as nat, next));
            assert(self.slot_from(tail, n, next)
                == self.next_slot(self.slot_from(tail, (n - 1) as nat, next),
                    tail[(n - 1) as int]));
        } else {
            assert(self.slot_from(sig, 1, slot) == self.next_slot(slot, sig[0]));
        }
    }

    /// Each virtual argument consumes one slot on a 64-bit ABI.
    proof fn lemma_slot_64(self, sig: Seq<PrimType>, n: nat, slot: nat)
        requires
            self == Arch::X86_64 || self == Arch::Aarch64,
            n <= sig.len(),
        ensures self.slot_from(sig, n, slot) == slot + n
        decreases n
    {
        if n > 0 {
            let next = self.next_slot(slot, sig[0]);
            self.lemma_slot_64(sig.drop_first(), (n - 1) as nat, next);
            assert(next == slot + 1);
        }
    }

    /// A 64-bit ABI reads virtual argument `n` directly from slot `n`.
    proof fn lemma_interp_64(self, args: Seq<u64>, sig: Seq<PrimType>, n: nat)
        requires
            self == Arch::X86_64 || self == Arch::Aarch64,
            n < sig.len(),
        ensures self.interp_args(args, sig)[n as int] == sig[n as int].cast(self, args[n as int])
    {
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

    /// x86 reads virtual argument `n` from its signature-derived physical slots.
    proof fn lemma_interp_x86_at(args: Seq<u64>, sig: Seq<PrimType>, n: nat, start: nat)
        requires
            n < sig.len(),
            start <= args.len(),
            Arch::X86.slot_at(sig, n, start) < args.len(),
            sig[n as int].bits(Arch::X86) == 64 ==>
                Arch::X86.slot_at(sig, n, start) + 1 < args.len(),
        ensures
            Self::interp_args_x86(args.skip(start as int), sig)[n as int]
                == sig[n as int].cast(Arch::X86,
                    Arch::X86.physical_value(args, sig, n, start)),
        decreases n
    {
        reveal_with_fuel(Arch::interp_args_x86, 2);
        if n == 0 {
            assert(Arch::X86.slot_at(sig, n, start) == start);
            assert(args.skip(start as int)[0] == args[start as int]);
            if sig[0].bits(Arch::X86) == 64 {
                assert(args.skip(start as int)[1] == args[(start + 1) as int]);
            }
        } else {
            let step: nat = if sig[0].bits(Arch::X86) == 64 { 2 } else { 1 };
            let next = start + step;
            let tail = sig.drop_first();
            Arch::X86.lemma_slot_lower(tail, (n - 1) as nat, next);
            assert(next <= Arch::X86.slot_at(sig, n, start));
            assert(next <= args.len());
            assert(Arch::X86.slot_at(tail, (n - 1) as nat, next)
                == Arch::X86.slot_at(sig, n, start));
            assert(tail[(n - 1) as int] == sig[n as int]);
            assert(args.skip(start as int).skip(step as int) =~= args.skip(next as int));
            Self::lemma_interp_x86_at(args, tail, (n - 1) as nat, next);
            Self::lemma_interp_x86_len(args.skip(start as int), sig);
            assert(Self::interp_args_x86(args.skip(start as int), sig)[n as int]
                == Self::interp_args_x86(args.skip(next as int), tail)[(n - 1) as int]);
            assert(Arch::X86.physical_value(args, sig, n, start)
                == Arch::X86.physical_value(args, tail, (n - 1) as nat, next));
        }
    }

    /// ARM reads virtual argument `n` from its aligned physical slots.
    proof fn lemma_interp_arm_at(args: Seq<u64>, sig: Seq<PrimType>, n: nat, start: nat)
        requires
            n < sig.len(),
            Arch::Arm.slot_at(sig, n, start) < args.len(),
            sig[n as int].bits(Arch::Arm) == 64 ==>
                Arch::Arm.slot_at(sig, n, start) + 1 < args.len(),
        ensures
            Self::interp_args_arm(args, sig, start as int)[n as int]
                == sig[n as int].cast(Arch::Arm,
                    Arch::Arm.physical_value(args, sig, n, start)),
        decreases n
    {
        reveal_with_fuel(Arch::interp_args_arm, 2);
        if n == 0 {
            assert(Arch::Arm.slot_at(sig, n, start)
                == if sig[0].bits(Arch::Arm) == 64 { start + start % 2 } else { start });
        } else {
            let next = Arch::Arm.next_slot(start, sig[0]);
            let tail = sig.drop_first();
            Arch::Arm.lemma_slot_lower(tail, (n - 1) as nat, next);
            assert(next <= Arch::Arm.slot_at(sig, n, start));
            assert(Arch::Arm.slot_at(tail, (n - 1) as nat, next)
                == Arch::Arm.slot_at(sig, n, start));
            assert(tail[(n - 1) as int] == sig[n as int]);
            Self::lemma_interp_arm_at(args, tail, (n - 1) as nat, next);
            Self::lemma_interp_arm_len(args, sig, start as int);
            assert(Self::interp_args_arm(args, sig, start as int)[n as int]
                == Self::interp_args_arm(args, tail, next as int)[(n - 1) as int]);
            assert(Arch::Arm.physical_value(args, sig, n, start)
                == Arch::Arm.physical_value(args, tail, (n - 1) as nat, next));
        }
    }

    /// Argument interpretation agrees with the signature-derived physical slots.
    proof fn lemma_interp_at(self, args: Seq<u64>, sig: Seq<PrimType>, n: nat)
        requires
            n < sig.len(),
            self.slot_for(sig, n) < args.len(),
            (self == Arch::X86 || self == Arch::Arm) && sig[n as int].bits(self) == 64 ==>
                self.slot_for(sig, n) + 1 < args.len(),
        ensures
            self.interp_args(args, sig)[n as int]
                == sig[n as int].cast(self, self.physical_value(args, sig, n, 0)),
    {
        match self {
            Arch::X86 => {
                Self::lemma_interp_x86_at(args, sig, n, 0);
                Self::lemma_interp_x86_len(args, sig);
                assert(args.skip(0) =~= args);
                assert(self.interp_args(args, sig) == Self::interp_args_x86(args, sig));
                assert(self.interp_args(args, sig)[n as int]
                    == sig[n as int].cast(self, self.physical_value(args, sig, n, 0)));
            }
            Arch::Arm => {
                Self::lemma_interp_arm_at(args, sig, n, 0);
                Self::lemma_interp_arm_len(args, sig, 0);
                assert(self.interp_args(args, sig) == Self::interp_args_arm(args, sig, 0));
                assert(self.interp_args(args, sig)[n as int]
                    == sig[n as int].cast(self, self.physical_value(args, sig, n, 0)));
            }
            Arch::X86_64 | Arch::Aarch64 => {
                self.lemma_slot_64(sig, n, 0);
                self.lemma_interp_64(args, sig, n);
                assert(self.slot_for(sig, n) == n);
                assert(self.interp_args(args, sig) == self.interp_args_64bit(args, sig));
                assert(self.interp_args(args, sig)[n as int]
                    == sig[n as int].cast(self, self.physical_value(args, sig, n, 0)));
            }
        }
    }

    /// The physical argument pattern has the low and high words in its selected slots.
    proof fn lemma_physical_words(self, args: Seq<u64>, sig: Seq<PrimType>,
        n: nat, slot: nat, low: u32, high: u32)
        requires
            n < sig.len(),
            sig[n as int].bits(self) == 64,
            slot == self.slot_for(sig, n),
            slot < args.len(),
            (self == Arch::X86 || self == Arch::Arm) ==> slot + 1 < args.len(),
            low == (args[slot as int] & 0xFFFF_FFFF) as u32,
            high == if self == Arch::X86 || self == Arch::Arm {
                (args[(slot + 1) as int] & 0xFFFF_FFFF) as u32
            } else {
                (args[slot as int] >> 32) as u32
            },
        ensures
            self.physical_value(args, sig, n, 0) as u32 == low,
            (self.physical_value(args, sig, n, 0) >> 32) as u32 == high,
    {
        assert(self.slot_at(sig, n, 0) == slot);
        if self == Arch::X86 || self == Arch::Arm {
            let l = args[slot as int];
            let h = args[(slot + 1) as int];
            assert(self.physical_value(args, sig, n, 0)
                == (l & 0xFFFF_FFFFu64) | ((h & 0xFFFF_FFFFu64) << 32u64));
            assert((((l & 0xFFFF_FFFFu64) | ((h & 0xFFFF_FFFFu64) << 32u64)) as u32)
                == (l & 0xFFFF_FFFFu64) as u32) by (bit_vector);
            assert(((((l & 0xFFFF_FFFFu64) | ((h & 0xFFFF_FFFFu64) << 32u64))
                >> 32u64) as u32) == (h & 0xFFFF_FFFFu64) as u32) by (bit_vector);
            assert(self.physical_value(args, sig, n, 0) as u32 == low);
            assert((self.physical_value(args, sig, n, 0) >> 32) as u32 == high);
        } else {
            assert(self.physical_value(args, sig, n, 0) == args[slot as int]);
            let raw = args[slot as int];
            assert(raw as u32 == (raw & 0xFFFF_FFFFu64) as u32) by (bit_vector);
            assert(self.physical_value(args, sig, n, 0) as u32 == low);
            assert((self.physical_value(args, sig, n, 0) >> 32) as u32 == high);
        }
    }

    /// The physical slot containing virtual argument `n`.
    spec fn slot_at(self, sig: Seq<PrimType>, n: nat, start: nat) -> nat {
        let slot = self.slot_from(sig, n, start);
        if self == Arch::Arm && sig[n as int].bits(self) == 64 {
            slot + slot % 2
        } else {
            slot
        }
    }

    /// The physical slot containing virtual argument `n`.
    spec fn slot_for(self, sig: Seq<PrimType>, n: nat) -> nat {
        self.slot_at(sig, n, 0)
    }

    /// The raw bit pattern of virtual argument `n`.
    spec fn physical_value(self, args: Seq<u64>, sig: Seq<PrimType>, n: nat, start: nat) -> u64 {
        let slot = self.slot_at(sig, n, start);
        if (self == Arch::X86 || self == Arch::Arm) && sig[n as int].bits(self) == 64 {
            (args[slot as int] & 0xFFFF_FFFFu64)
                | ((args[(slot + 1) as int] & 0xFFFF_FFFFu64) << 32u64)
        } else {
            args[slot as int]
        }
    }

    /// A prefix never moves the next free slot backward.
    proof fn lemma_slot_lower(self, sig: Seq<PrimType>, n: nat, start: nat)
        requires n <= sig.len()
        ensures self.slot_from(sig, n, start) >= start
        decreases n
    {
        if n > 0 {
            let next = self.next_slot(start, sig[0]);
            self.lemma_slot_lower(sig.drop_first(), (n - 1) as nat, next);
            assert(next >= start);
        }
    }

    /// Whether the architecture has 64-bit argument slots.
    fn is_64bit(self) -> (res: bool)
        ensures res == (self == Arch::X86_64 || self == Arch::Aarch64)
    {
        self == Arch::X86_64 || self == Arch::Aarch64
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

impl Action {
    /// Executable version of [`Action::precedence`].
    pub(super) fn priority(&self) -> (res: u8)
        ensures res == self.precedence()
    {
        match self {
            Action::KillProcess => 7,
            Action::KillThread => 6,
            Action::Trap(_) => 5,
            Action::Errno(_) => 4,
            Action::Notify => 3,
            Action::Trace(_) => 2,
            Action::Log => 1,
            Action::Allow => 0,
        }
    }

    /// Executable version of [`Action::to_ret`].
    pub(super) fn exec_to_ret(&self) -> (res: u32)
        ensures res == self.to_ret()
    {
        match self {
            Action::KillProcess => Self::RET_KILL_PROCESS,
            Action::KillThread => Self::RET_KILL_THREAD,
            Action::Trap(data) => Self::RET_TRAP | *data as u32,
            Action::Errno(data) => Self::RET_ERRNO | *data as u32,
            Action::Trace(data) => Self::RET_TRACE | *data as u32,
            Action::Log => Self::RET_LOG,
            Action::Allow => Self::RET_ALLOW,
            Action::Notify => Self::RET_USER_NOTIF,
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
}

impl ArgCmp {
    /// The landing point selected by one argument test.
    spec fn word_target(self, arch: Arch, syscall: Syscall, args: Seq<u64>,
        pass: nat, fail: nat) -> nat {
        if self.eval(arch, syscall, args) { pass } else { fail }
    }

    /// Typed evaluation reads the physical slots selected by the signature.
    proof fn lemma_eval_physical(self, arch: Arch, syscall: Syscall, args: Seq<u64>,
        sig: Seq<PrimType>)
        requires
            self.wf(arch, syscall),
            sig =~= syscall.spec_signature(arch),
            arch.slot_for(sig, self.arg as nat) < args.len(),
            (arch == Arch::X86 || arch == Arch::Arm)
                && sig[self.arg as int].bits(arch) == 64 ==>
                arch.slot_for(sig, self.arg as nat) + 1 < args.len(),
        ensures
            self.eval(arch, syscall, args)
                <==> self.typed_test(arch, sig[self.arg as int],
                    arch.physical_value(args, sig, self.arg as nat, 0)),
    {
        arch.lemma_interp_at(args, sig, self.arg as nat);
    }

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

    /// The result of the emitted one-word comparison on a raw bit pattern.
    spec fn word_test(self, arch: Arch, ty: PrimType, value: u64) -> bool {
        let width = ty.bits(arch);
        let mask: u32 = if width == 16 { 0xFFFF } else { u32::MAX };
        let order = self.op is Lt || self.op is Le || self.op is Gt || self.op is Ge;
        let bias: u32 = if ty.signed() && order {
            if width == 16 { 0x8000 } else { 0x8000_0000 }
        } else { 0 };
        let x = ((value as u32) & mask) ^ bias;
        let a = ((self.a as u32) & mask) ^ bias;
        match self.op {
            Compare::Eq => x == a,
            Compare::Ne => x != a,
            Compare::Lt => x < a,
            Compare::Le => x <= a,
            Compare::Ge => x >= a,
            Compare::Gt => x > a,
            Compare::MaskedEq => (value as u32) & (self.a as u32) == self.b as u32,
        }
    }

    /// The result of the emitted two-word comparison on a raw bit pattern.
    spec fn wide_test(self, arch: Arch, ty: PrimType, low: u32, high: u32) -> bool {
        let order = self.op is Lt || self.op is Le || self.op is Gt || self.op is Ge;
        let bias: u32 = if ty.signed() && order { 0x8000_0000 } else { 0 };
        self.wide_words(low, high ^ bias, bias)
    }

    /// The two-word comparison after an optional sign-bit flip of the high word.
    spec fn wide_words(self, low: u32, high: u32, bias: u32) -> bool {
        let h = high;
        let a_hi = ((self.a >> 32) as u32) ^ bias;
        let a_lo = self.a as u32;
        match self.op {
            Compare::Eq => h == a_hi && low == a_lo,
            Compare::Ne => h != a_hi || low != a_lo,
            Compare::Lt => h < a_hi || (h == a_hi && low < a_lo),
            Compare::Le => h < a_hi || (h == a_hi && low <= a_lo),
            Compare::Gt => h > a_hi || (h == a_hi && low > a_lo),
            Compare::Ge => h > a_hi || (h == a_hi && low >= a_lo),
            Compare::MaskedEq =>
                (high & ((self.a >> 32) as u32) == (self.b >> 32) as u32)
                    && (low & (self.a as u32) == self.b as u32),
        }
    }

    /// The landing point selected by a two-word comparison.
    spec fn wide_target(self, low: u32, high: u32, bias: u32,
        pass: nat, fail: nat) -> nat {
        if self.wide_words(low, high, bias) { pass } else { fail }
    }

    /// The target when the high word exceeds the comparison value.
    spec fn high_gt_target(self, pass: nat, fail: nat) -> nat {
        if self.op is Lt || self.op is Le { fail } else { pass }
    }

    /// The target when unequal high words reach the equality test.
    spec fn high_neq_target(self, pass: nat, fail: nat) -> nat {
        if self.op is Ne || self.op is Lt || self.op is Le { pass } else { fail }
    }

    /// Typed comparison agrees with the two-word instruction condition.
    proof fn lemma_wide_truth(self, arch: Arch, syscall: Syscall, sig: Seq<PrimType>,
        args: Seq<u64>, slot: u32)
        requires
            self.wf(arch, syscall),
            sig =~= syscall.spec_signature(arch),
            slot as nat == arch.slot_for(sig, self.arg as nat),
            slot < args.len(),
            sig[self.arg as int].bits(arch) == 64,
            (arch == Arch::X86 || arch == Arch::Arm) ==> slot + 1 < args.len(),
        ensures
            self.eval(arch, syscall, args) <==> {
                let x = arch.physical_value(args, sig, self.arg as nat, 0);
                self.wide_test(arch, sig[self.arg as int], x as u32, (x >> 32) as u32)
            },
    {
        reveal(ArgCmp::typed_test);
        reveal(ArgCmp::wide_test);
        let ty = sig[self.arg as int];
        self.lemma_eval_physical(arch, syscall, args, sig);
        let x = arch.physical_value(args, sig, self.arg as nat, 0);
        let a = self.a;
        assert(ty.mask(arch) == u64::MAX);
        assert((x & u64::MAX) == x) by (bit_vector);
        assert((a & u64::MAX) == a) by (bit_vector);
        let high = (x >> 32) as u32;
        let a_high = (a >> 32) as u32;
        assert((high ^ 0u32) == high) by (bit_vector);
        assert((a_high ^ 0u32) == a_high) by (bit_vector);
        if self.op is Eq || self.op is Ne {
            ty.lemma_cast_eq(arch, x, a);
            Self::lemma_words(x, a);
            assert(self.typed_test(arch, ty, x)
                <==> self.wide_test(arch, ty, x as u32, (x >> 32) as u32));
        } else if self.op is MaskedEq {
            ty.lemma_cast_bits(arch, x);
            Self::lemma_words(x, a);
            Self::lemma_words(x & a, self.b);
            assert(self.typed_test(arch, ty, x)
                <==> self.wide_test(arch, ty, x as u32, (x >> 32) as u32));
        } else if ty.signed() {
            ty.lemma_signed_bias_64(arch, x, a);
            ty.lemma_signed_bias_64(arch, a, x);
            let sign = 0x8000_0000_0000_0000u64;
            let bx = x ^ sign;
            let ba = a ^ sign;
            Self::lemma_words(bx, ba);
            assert((((x ^ sign) >> 32) as u32)
                == (((x >> 32) as u32) ^ 0x8000_0000u32))
                by (bit_vector) requires sign == 0x8000_0000_0000_0000u64;
            assert((((a ^ sign) >> 32) as u32)
                == (((a >> 32) as u32) ^ 0x8000_0000u32))
                by (bit_vector) requires sign == 0x8000_0000_0000_0000u64;
            assert(((x ^ sign) as u32) == (x as u32)) by (bit_vector)
                requires sign == 0x8000_0000_0000_0000u64;
            assert(((a ^ sign) as u32) == (a as u32)) by (bit_vector)
                requires sign == 0x8000_0000_0000_0000u64;
            assert(self.typed_test(arch, ty, x)
                <==> self.wide_test(arch, ty, x as u32, (x >> 32) as u32));
        } else {
            Self::lemma_words(x, a);
            assert(!ty.signed());
            assert(ty.cast(arch, x) == x as int);
            assert(ty.cast(arch, a) == a as int);
            assert(self.typed_test(arch, ty, x)
                <==> self.wide_test(arch, ty, x as u32, (x >> 32) as u32));
        }
    }

    /// Typed comparison agrees with the one-word instruction condition.
    proof fn lemma_word_truth(self, arch: Arch, syscall: Syscall, sig: Seq<PrimType>,
        args: Seq<u64>, slot: u32, width: u32)
        requires
            self.wf(arch, syscall),
            sig =~= syscall.spec_signature(arch),
            slot as nat == arch.slot_for(sig, self.arg as nat),
            slot < args.len(),
            width as u64 == sig[self.arg as int].bits(arch),
            width == 16 || width == 32,
        ensures
            self.eval(arch, syscall, args)
                <==> self.word_test(arch, sig[self.arg as int], args[slot as int]),
    {
        reveal(ArgCmp::typed_test);
        reveal(ArgCmp::word_test);
        let ty = sig[self.arg as int];
        self.lemma_eval_physical(arch, syscall, args, sig);
        let x = arch.physical_value(args, sig, self.arg as nat, 0);
        assert(x == args[slot as int]);
        if ty.bits(arch) == 16 {
            assert(((1u64 << 16u64) - 1) == 0xFFFF) by (bit_vector);
            assert(ty.mask(arch) == 0xFFFF);
        } else {
            assert(((1u64 << 32u64) - 1) == 0xFFFF_FFFF) by (bit_vector);
            assert(ty.mask(arch) == 0xFFFF_FFFF);
        }
        let mask: u32 = if width == 16 { 0xFFFF } else { u32::MAX };
        let a = self.a;
        let xv = x;
        assert(ty.mask(arch) == mask as u64);
        assert(((xv & (mask as u64)) as u32) == ((xv as u32) & mask))
            by (bit_vector);
        assert(((a & (mask as u64)) as u32) == ((a as u32) & mask))
            by (bit_vector);
        assert((xv & (mask as u64) == a & (mask as u64))
            <==> (((xv as u32) & mask) == ((a as u32) & mask))) by (bit_vector);
        let low_x = (x as u32) & mask;
        let low_a = (a as u32) & mask;
        assert((low_x ^ 0u32) == low_x) by (bit_vector);
        assert((low_a ^ 0u32) == low_a) by (bit_vector);
        if self.op is Eq || self.op is Ne {
            ty.lemma_cast_eq(arch, x, self.a);
            assert(!(self.op is Lt || self.op is Le || self.op is Gt || self.op is Ge));
            assert(ty.bits(arch) == width as u64);
            assert((if ty.bits(arch) == 16 { 0xFFFFu32 } else { u32::MAX }) == mask);
            assert((ty.cast(arch, x) == ty.cast(arch, a))
                <==> (x & ty.mask(arch) == a & ty.mask(arch)));
            assert((ty.cast(arch, x) == ty.cast(arch, a))
                <==> (((x as u32) & mask) == ((a as u32) & mask)));
            if self.op is Eq {
                assert(self.typed_test(arch, ty, x)
                    == (ty.cast(arch, x) == ty.cast(arch, a)));
                assert(self.word_test(arch, ty, x)
                    == (((x as u32) & mask) == ((a as u32) & mask)));
            } else {
                assert(self.typed_test(arch, ty, x)
                    == (ty.cast(arch, x) != ty.cast(arch, a)));
                assert(self.word_test(arch, ty, x)
                    == (((x as u32) & mask) != ((a as u32) & mask)));
            }
            assert(self.typed_test(arch, ty, x) <==> self.word_test(arch, ty, x));
        } else if self.op is MaskedEq {
            ty.lemma_cast_bits(arch, x);
            let m = ty.mask(arch);
            let b = self.b;
            assert(((xv & m) & a == b) <==> (((xv as u32) & (a as u32)) == (b as u32)))
                by (bit_vector)
                requires a & !m == 0, b & !a == 0, m == 0xFFFF || m == 0xFFFF_FFFF;
            assert(self.typed_test(arch, ty, x) <==> self.word_test(arch, ty, x));
        } else if ty.signed() {
            ty.lemma_signed_bias(arch, x, self.a);
            ty.lemma_signed_bias(arch, self.a, x);
            let type_mask = ty.mask(arch);
            let bias64: u64 = ((type_mask >> 1u64) + 1) as u64;
            let bias32: u32 = if width == 16 { 0x8000 } else { 0x8000_0000 };
            if width == 16 {
                assert((type_mask >> 1u64) == 0x7FFF) by (bit_vector)
                    requires type_mask == 0xFFFF;
            } else {
                assert((type_mask >> 1u64) == 0x7FFF_FFFF) by (bit_vector)
                    requires type_mask == 0xFFFF_FFFF;
            }
            assert(bias64 == bias32 as u64);
            assert(((((x & (mask as u64)) ^ (bias32 as u64)) as u32)
                == (((x as u32) & mask) ^ bias32)))
                by (bit_vector)
                requires type_mask == mask as u64, bias64 == bias32 as u64;
            assert(((((a & (mask as u64)) ^ (bias32 as u64)) as u32)
                == (((a as u32) & mask) ^ bias32)))
                by (bit_vector)
                requires type_mask == mask as u64, bias64 == bias32 as u64;
            assert(self.typed_test(arch, ty, x) <==> self.word_test(arch, ty, x));
        } else {
            assert(ty.cast(arch, x) == (x & ty.mask(arch)) as int);
            assert(ty.cast(arch, a) == (a & ty.mask(arch)) as int);
            assert((x & (mask as u64)) == (((x as u32) & mask) as u64)) by (bit_vector);
            assert((a & (mask as u64)) == (((a as u32) & mask) as u64)) by (bit_vector);
            assert(self.typed_test(arch, ty, x) <==> self.word_test(arch, ty, x));
        }
    }

    /// The load at the front of `ext` hands the word it reads to the code behind it.
    proof fn lemma_load(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], k: u32, a: u32, to: nat)
        requires
            ext == rev.push(Instr::LdAbs(k)),
            k + 4 <= data@.len(),
            Builder::lands(rev, data, rev.len(), Builder::word(data, k), to),
        ensures Builder::lands(ext, data, ext.len(), a, to)
    {
        assert(Builder::extends(rev, ext));
        assert(ext[ext.len() - 1] == Instr::LdAbs(k));
        Builder::lemma_ld(ext, k);
        assert(Builder::goes_to(ext, data, ext.len(), a, rev.len(), Builder::word(data, k)));
        Builder::lemma_then(rev, ext, data, ext.len(), a, rev.len(),
            Builder::word(data, k), to, 0);
    }

    /// A landing behind `rev` is still one once the code in front of it has carried on there.
    proof fn lemma_step(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], a: u32, mid: nat, m: u32, to: nat)
        requires
            Builder::extends(rev, ext),
            Builder::goes_to(ext, data, ext.len(), a, mid, m),
            Builder::lands(rev, data, mid, m, to),
        ensures Builder::lands(ext, data, ext.len(), a, to)
    {
        Builder::lemma_then(rev, ext, data, ext.len(), a, mid, m, to, 0);
    }

    /// The mask at the front of `ext` hands the masked word to the code behind it.
    proof fn lemma_mask(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], k: u32, a: u32)
        requires ext == rev.push(Instr::Alu(AluOp::And, Src::K(k)))
        ensures Builder::goes_to(ext, data, ext.len(), a, rev.len(), a & k)
    {
        Builder::lemma_alu(ext, AluOp::And, k);
        assert(Builder::goes_to(ext, data, ext.len(), a, (ext.len() - 1) as nat,
            AluOp::And.eval(a, k)));
    }

    /// The two-word test lands where its high word, and then its low word, send it.
    proof fn lemma_branch(self, s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>,
        s4: Seq<Instr>, s5: Seq<Instr>, s6: Seq<Instr>, lo: u32, bias: u32,
        k_lo: u32, k_hi: u32, pass: nat, fail: nat)
        requires
            lo <= 60,
            k_lo == if self.op is MaskedEq { self.b as u32 } else { self.a as u32 },
            k_hi == if self.op is MaskedEq { (self.b >> 32) as u32 }
                else { ((self.a >> 32) as u32) ^ bias },
            s2 == if self.op is MaskedEq {
                s1.push(Instr::Alu(AluOp::And, Src::K(self.a as u32)))
            } else { s1 },
            s3 == s2.push(Instr::LdAbs(lo)),
            Builder::extends(s3, s4),
            Builder::extends(s4, s5),
            s6 == if self.op is MaskedEq {
                s5.push(Instr::Alu(AluOp::And, Src::K((self.a >> 32) as u32)))
            } else { s5 },
            forall |data: &[u8], a: u32| !self.op.holds(a, k_lo) ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, fail, a),
            forall |data: &[u8], a: u32| self.op.holds(a, k_lo) ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, pass, a),
            forall |data: &[u8], h: u32| h == k_hi ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), h, s3.len(), h),
            forall |data: &[u8], h: u32| h != k_hi ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), h,
                    self.high_neq_target(pass, fail), h),
            (self.op is Lt || self.op is Le || self.op is Gt || self.op is Ge) ==> {
                &&& forall |data: &[u8], h: u32| h > k_hi ==>
                    #[trigger] Builder::goes_to(s5, data, s5.len(), h,
                        self.high_gt_target(pass, fail), h)
                &&& forall |data: &[u8], h: u32| h <= k_hi ==>
                    #[trigger] Builder::goes_to(s5, data, s5.len(), h, s4.len(), h)
            },
            !(self.op is Lt || self.op is Le || self.op is Gt || self.op is Ge) ==> s5 == s4,
        ensures
            forall |data: &[u8], h: u32| Event::parse(data) is Some ==>
                #[trigger] Builder::lands(s6, data, s6.len(), h,
                    self.wide_target(Builder::word(data, lo), h, bias, pass, fail)),
    {
        let masked = self.op is MaskedEq;
        let order = self.op is Lt || self.op is Le || self.op is Gt || self.op is Ge;
        let a_lo = self.a as u32;
        let a_hi = (self.a >> 32) as u32;
        assert forall |data: &[u8], h: u32| Event::parse(data) is Some implies
            #[trigger] Builder::lands(s6, data, s6.len(), h,
                self.wide_target(Builder::word(data, lo), h, bias, pass, fail)) by {
            let low = Builder::word(data, lo);
            let target = self.wide_target(low, h, bias, pass, fail);
            let l = if masked { low & a_lo } else { low };
            let m = if masked { h & a_hi } else { h };
            if m == k_hi {
                if self.op.holds(l, k_lo) {
                    assert(target == pass);
                    assert(Builder::goes_to(s1, data, s1.len(), l, pass, l));
                } else {
                    assert(target == fail);
                    assert(Builder::goes_to(s1, data, s1.len(), l, fail, l));
                }
                assert(Builder::lands(s1, data, s1.len(), l, target));
                if masked {
                    Self::lemma_mask(s1, s2, data, a_lo, low);
                    Self::lemma_step(s1, s2, data, low, s1.len(), l, target);
                }
                assert(Builder::lands(s2, data, s2.len(), low, target));
                Self::lemma_load(s2, s3, data, lo, m, target);
                assert(Builder::goes_to(s4, data, s4.len(), m, s3.len(), m));
                Self::lemma_step(s3, s4, data, m, s3.len(), m, target);
            } else if order && m > k_hi {
                assert(target == self.high_gt_target(pass, fail));
                assert(Builder::goes_to(s5, data, s5.len(), m, target, m));
            } else {
                assert(target == self.high_neq_target(pass, fail));
                assert(Builder::goes_to(s4, data, s4.len(), m, target, m));
            }
            if order && m <= k_hi {
                assert(Builder::goes_to(s5, data, s5.len(), m, s4.len(), m));
                Self::lemma_step(s4, s5, data, m, s4.len(), m, target);
            }
            assert(Builder::lands(s5, data, s5.len(), m, target));
            if masked {
                Self::lemma_mask(s5, s6, data, a_hi, h);
                Self::lemma_step(s5, s6, data, h, s5.len(), m, target);
            }
        }
    }
}

impl ArgCmp {
    /// Emits a typed argument comparison using the syscall's physical argument slots.
    fn emit(&self, b: &mut Builder, arch: Arch, syscall: Syscall,
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
        let mut slot: u32 = 0;
        let mut i: usize = 0;
        while i < self.arg as usize
            invariant
                i <= self.arg as usize,
                i <= sig@.len(),
                slot <= Rule::ARG_COUNT_MAX,
                slot as nat == arch.slot_before(sig@, i as nat),
                self.wf(arch, syscall),
                sig@ =~= syscall.spec_signature(arch),
                b.wf(),
                0 < fail <= b.rev@.len(),
            decreases (self.arg as usize) - i
        {
            let width = sig[i].exec_bits(arch);
            if (arch == Arch::X86 || arch == Arch::Arm) && width == 64 {
                if arch == Arch::Arm && !slot.is_multiple_of(2) {
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
                arch.lemma_slot_next(sig@, i as nat, 0);
                assert(slot as nat == arch.slot_before(sig@, (i + 1) as nat));
            }
            i += 1;
        }
        let ty = sig[self.arg as usize];
        let width = ty.exec_bits(arch);
        if width != 16 && width != 32 && width != 64 {
            return Err(CompileError::UnsupportedArgWidth(width));
        }
        if arch == Arch::Arm && width == 64 && !slot.is_multiple_of(2) {
            slot += 1;
        }
        proof {
            assert(slot as nat == arch.slot_for(sig@, self.arg as nat));
        }
        if slot >= Rule::ARG_COUNT_MAX
            || width == 64 && !arch.is_64bit() && slot > 4 {
            return Err(CompileError::SignatureLayout);
        }

        let order = self.op == Compare::Lt || self.op == Compare::Le
            || self.op == Compare::Gt || self.op == Compare::Ge;
        let signed_order = ty.exec_signed() && order;
        if width <= 32 {
            self.emit_word(b, arch, syscall, sig, slot, width, signed_order, fail)
        } else {
            self.emit_wide(b, arch, syscall, sig, slot, signed_order, fail)
        }
    }

    /// Emits a comparison of an argument that fits in one word.
    ///
    /// ```text
    ///     ld  [lo]
    ///     and #0xffff             ; 16-bit, not MaskedEq
    ///     xor #bias               ; signed ordering
    ///     and #a                  ; MaskedEq
    ///     j!<op> #k -> fail
    /// ```
    #[allow(clippy::too_many_arguments)]
    fn emit_word(&self, b: &mut Builder, _arch: Arch, _syscall: Syscall,
        _sig: &[PrimType], slot: u32, width: u32, signed_order: bool,
        fail: Label) -> (res: Result<(), CompileError>)
        requires
            self.wf(_arch, _syscall),
            _sig@ =~= _syscall.spec_signature(_arch),
            slot as nat == _arch.slot_for(_sig@, self.arg as nat),
            slot < Rule::ARG_COUNT_MAX,
            width == 16 || width == 32,
            width as u64 == _sig@[self.arg as int].bits(_arch),
            signed_order == (_sig@[self.arg as int].signed() &&
                (self.op is Lt || self.op is Le || self.op is Gt || self.op is Ge)),
            0 < fail <= b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.eval(_arch, _syscall, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, old(b).rev@.len()),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.eval(_arch, _syscall, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, fail as nat),
    {
        let ghost pass: nat = b.rev@.len();
        let lo = Policy::OFFSET_EVENT_ARGS + 8 * slot;
        let masked = self.op == Compare::MaskedEq;
        let mask: u32 = if width == 16 { 0xFFFF } else { u32::MAX };
        let bias: u32 = if signed_order {
            if width == 16 { 0x8000 } else { 0x8000_0000 }
        } else { 0 };
        let k = if masked { self.b as u32 } else { (self.a as u32 & mask) ^ bias };
        let (jmp, expect) = self.op.fail_jump();
        b.emit_jump(jmp, Src::K(k), expect, fail)?;
        let ghost r_jump = b.rev@;
        if masked {
            b.emit(Instr::Alu(AluOp::And, Src::K(self.a as u32)));
        } else if signed_order {
            b.emit(Instr::Alu(AluOp::Xor, Src::K(bias)));
        }
        let ghost r_xor = b.rev@;
        if !masked && width < 32 {
            b.emit(Instr::Alu(AluOp::And, Src::K(mask)));
        }
        let ghost r_and = b.rev@;
        b.emit(Instr::LdAbs(lo));
        proof {
            assert forall |data: &[u8], incoming: u32| Event::parse(data) is Some implies
                #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), incoming,
                    self.word_target(_arch, _syscall, Event::of(data).args,
                        pass as nat, fail as nat)) by {
                let ev = Event::of(data);
                Event::lemma_image(data);
                self.lemma_word_truth(_arch, _syscall, _sig@, ev.args, slot, width);
                let raw = ev.args[slot as int];
                let word = Builder::word(data, lo);
                assert(word == (raw & 0xFFFF_FFFF) as u32);
                assert((raw & 0xFFFF_FFFF) as u32 == raw as u32) by (bit_vector);
                assert((word & u32::MAX) == word) by (bit_vector);
                let narrowed = if !masked && width == 16 { word & mask } else { word };
                let tested = if masked { narrowed & (self.a as u32) }
                    else if signed_order { narrowed ^ bias } else { narrowed };
                let target = self.word_target(_arch, _syscall, ev.args,
                    pass as nat, fail as nat);
                assert((narrowed ^ 0u32) == narrowed) by (bit_vector);
                assert(self.eval(_arch, _syscall, ev.args) == self.op.holds(tested, k));
                if self.op.holds(tested, k) {
                    assert(Builder::goes_to(r_jump, data, r_jump.len(), tested, pass, tested));
                } else {
                    assert(Builder::goes_to(r_jump, data, r_jump.len(), tested, fail as nat,
                        tested));
                }
                assert(Builder::lands(r_jump, data, r_jump.len(), tested, target));
                if masked {
                    Self::lemma_mask(r_jump, r_xor, data, self.a as u32, word);
                    Self::lemma_step(r_jump, r_xor, data, word, r_jump.len(), tested, target);
                } else if signed_order {
                    Builder::lemma_alu(r_xor, AluOp::Xor, bias);
                    assert(Builder::goes_to(r_xor, data, r_xor.len(), narrowed,
                        r_jump.len(), tested));
                    Self::lemma_step(r_jump, r_xor, data, narrowed, r_jump.len(),
                        tested, target);
                } else {
                    assert(r_xor == r_jump);
                }
                if !masked && width == 16 {
                    Self::lemma_mask(r_xor, r_and, data, mask, word);
                    Self::lemma_step(r_xor, r_and, data, word, r_xor.len(),
                        narrowed, target);
                } else {
                    assert(r_and == r_xor);
                }
                Self::lemma_load(r_and, b.rev@, data, lo, incoming, target);
            }
            assert forall |data: &[u8], incoming: u32|
                Event::parse(data) is Some
                    && self.eval(_arch, _syscall, Event::of(data).args)
                implies #[trigger] Builder::lands(b.rev@, data, b.rev@.len(),
                    incoming, pass as nat) by {
                assert(Builder::lands(b.rev@, data, b.rev@.len(), incoming,
                    self.word_target(_arch, _syscall, Event::of(data).args,
                        pass as nat, fail as nat)));
            }
            assert forall |data: &[u8], incoming: u32|
                Event::parse(data) is Some
                    && !self.eval(_arch, _syscall, Event::of(data).args)
                implies #[trigger] Builder::lands(b.rev@, data, b.rev@.len(),
                    incoming, fail as nat) by {
                assert(Builder::lands(b.rev@, data, b.rev@.len(), incoming,
                    self.word_target(_arch, _syscall, Event::of(data).args,
                        pass as nat, fail as nat)));
            }
        }
        Ok(())
    }

    /// Emits a two-word comparison for a 64-bit argument.
    ///
    /// ```text
    ///     ld  [hi]
    ///     xor #0x80000000         ; signed ordering
    ///     and #a_hi               ; MaskedEq
    ///     jgt #k_hi -> gt         ; ordering
    ///     jne #k_hi -> neq
    ///     ld  [lo]
    ///     and #a_lo               ; MaskedEq
    ///     j!<op> #k_lo -> fail
    /// ```
    #[allow(clippy::too_many_arguments)]
    #[verifier::spinoff_prover]
    fn emit_wide(&self, b: &mut Builder, arch: Arch, _syscall: Syscall,
        _sig: &[PrimType], slot: u32, signed_order: bool,
        fail: Label) -> (res: Result<(), CompileError>)
        requires
            self.wf(arch, _syscall),
            _sig@ =~= _syscall.spec_signature(arch),
            slot as nat == arch.slot_for(_sig@, self.arg as nat),
            slot < Rule::ARG_COUNT_MAX,
            _sig@[self.arg as int].bits(arch) == 64,
            (arch == Arch::X86 || arch == Arch::Arm) ==> slot + 1 < Rule::ARG_COUNT_MAX,
            signed_order == (_sig@[self.arg as int].signed() &&
                (self.op is Lt || self.op is Le || self.op is Gt || self.op is Ge)),
            0 < fail <= b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.eval(arch, _syscall, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, old(b).rev@.len()),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.eval(arch, _syscall, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, fail as nat),
    {
        let pass = b.label();
        let lo = Policy::OFFSET_EVENT_ARGS + 8 * slot;
        let hi = if arch.is_64bit() { lo + 4 } else { lo + 8 };
        let masked = self.op == Compare::MaskedEq;
        let order = self.op == Compare::Lt || self.op == Compare::Le
            || self.op == Compare::Gt || self.op == Compare::Ge;
        let below = self.op == Compare::Ne || self.op == Compare::Lt || self.op == Compare::Le;
        let neq = if below { pass } else { fail };
        let gt = if below { fail } else { pass };
        let bias: u32 = if signed_order { 0x8000_0000 } else { 0 };
        let a_lo = self.a as u32;
        let a_hi = (self.a >> 32) as u32;
        let k_lo = if masked { self.b as u32 } else { a_lo };
        let k_hi = if masked { (self.b >> 32) as u32 } else { a_hi ^ bias };
        let (jmp, expect) = self.op.fail_jump();
        b.emit_jump(jmp, Src::K(k_lo), expect, fail)?;
        let ghost s1 = b.rev@;
        if masked {
            b.emit(Instr::Alu(AluOp::And, Src::K(a_lo)));
        }
        let ghost s2 = b.rev@;
        b.emit(Instr::LdAbs(lo));
        let ghost s3 = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(k_hi), false, neq)?;
        let ghost s4 = b.rev@;
        if order {
            b.emit_jump(JmpOp::Gt, Src::K(k_hi), true, gt)?;
        }
        let ghost s5 = b.rev@;
        if masked {
            b.emit(Instr::Alu(AluOp::And, Src::K(a_hi)));
        }
        let ghost r_branch = b.rev@;
        proof {
            assert(neq as nat == self.high_neq_target(pass as nat, fail as nat));
            assert(order ==> gt as nat == self.high_gt_target(pass as nat, fail as nat));
            self.lemma_branch(s1, s2, s3, s4, s5, r_branch, lo, bias, k_lo, k_hi,
                pass as nat, fail as nat);
        }
        if signed_order {
            b.emit(Instr::Alu(AluOp::Xor, Src::K(bias)));
        }
        let ghost r_xor = b.rev@;
        b.emit(Instr::LdAbs(hi));
        proof {
            assert forall |data: &[u8], incoming: u32| Event::parse(data) is Some implies
                #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), incoming,
                    self.word_target(arch, _syscall, Event::of(data).args,
                        pass as nat, fail as nat)) by {
                let ev = Event::of(data);
                Event::lemma_image(data);
                self.lemma_wide_truth(arch, _syscall, _sig@, ev.args, slot);
                let low = Builder::word(data, lo);
                let high = Builder::word(data, hi);
                assert(low == (ev.args[slot as int] & 0xFFFF_FFFF) as u32);
                if arch == Arch::X86_64 || arch == Arch::Aarch64 {
                    assert(high == (ev.args[slot as int] >> 32) as u32);
                } else {
                    assert(high == (ev.args[(slot + 1) as int] & 0xFFFF_FFFF) as u32);
                }
                arch.lemma_physical_words(ev.args, _sig@, self.arg as nat,
                    slot as nat, low, high);
                let x = arch.physical_value(ev.args, _sig@, self.arg as nat, 0);
                let ty = _sig@[self.arg as int];
                let tested_high = high ^ bias;
                let target = self.word_target(arch, _syscall, ev.args,
                    pass as nat, fail as nat);
                let branch_target = self.wide_target(low, tested_high, bias,
                    pass as nat, fail as nat);
                assert(self.eval(arch, _syscall, ev.args)
                    == self.wide_test(arch, ty, low, high));
                assert(branch_target == target);
                assert(Builder::lands(r_branch, data, r_branch.len(),
                    tested_high, target));
                if signed_order {
                    Builder::lemma_alu(r_xor, AluOp::Xor, bias);
                    assert(Builder::goes_to(r_xor, data, r_xor.len(), high,
                        r_branch.len(), tested_high));
                    Self::lemma_step(r_branch, r_xor, data, high,
                        r_branch.len(), tested_high, target);
                } else {
                    assert(r_xor == r_branch);
                    assert((high ^ 0u32) == high) by (bit_vector);
                }
                assert(hi + 4 <= data@.len());
                Self::lemma_load(r_xor, b.rev@, data, hi, incoming, target);
            }
            assert forall |data: &[u8], incoming: u32|
                Event::parse(data) is Some
                    && self.eval(arch, _syscall, Event::of(data).args)
                implies #[trigger] Builder::lands(b.rev@, data, b.rev@.len(),
                    incoming, pass as nat) by {
                assert(Builder::lands(b.rev@, data, b.rev@.len(), incoming,
                    self.word_target(arch, _syscall, Event::of(data).args,
                        pass as nat, fail as nat)));
            }
            assert forall |data: &[u8], incoming: u32|
                Event::parse(data) is Some
                    && !self.eval(arch, _syscall, Event::of(data).args)
                implies #[trigger] Builder::lands(b.rev@, data, b.rev@.len(),
                    incoming, fail as nat) by {
                assert(Builder::lands(b.rev@, data, b.rev@.len(), incoming,
                    self.word_target(arch, _syscall, Event::of(data).args,
                        pass as nat, fail as nat)));
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
                b.emit_jump(JmpOp::Eq, Src::K(arg), false, end)?;
                let ghost r_sel = b.rev@;
                let is_ipc = self.syscall.ipc_arg().is_some();
                if is_ipc {
                    b.emit(Instr::Alu(AluOp::And, Src::K(0xFFFF)));
                }
                let ghost r_mask = b.rev@;
                let ghost r_arg = r_mask.push(Instr::LdAbs(Policy::OFFSET_EVENT_ARGS));
                proof {
                    Builder::lemma_ld(r_arg, Policy::OFFSET_EVENT_ARGS);
                    assert forall |data: &[u8], a: u32|
                        Event::parse(data) is Some
                        && self.body_holds(arch, nr, Event::of(data))
                        implies #[trigger] Builder::returns(r_arg, data, r_arg.len(), a,
                            self.action.to_ret()) by {
                        Event::lemma_image(data);
                        assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * 0) as u32)
                            == (Event::of(data).args[0] & 0xFFFF_FFFF) as u32);
                        let w = Builder::word(data, Policy::OFFSET_EVENT_ARGS);
                        let selector = if is_ipc { w & 0xFFFF } else { w };
                        Self::lemma_ipc_selector(Event::of(data).args[0]);
                        assert(selector == arg);
                        assert(Builder::goes_to_all(r_arg, data, r_arg.len(),
                            (r_arg.len() - 1) as nat, w));
                        assert(Builder::goes_to(r_arg, data, r_arg.len(), a, r_mask.len(), w));
                        assert(Builder::goes_to(r_sel, data, r_sel.len(), selector,
                            r_ret.len(), selector));
                        Builder::lemma_then(r_ret, r_sel, data, r_sel.len(), selector,
                            r_ret.len(), selector,
                            0, self.action.to_ret());
                        if is_ipc {
                            Builder::lemma_alu(r_mask, AluOp::And, 0xFFFF);
                            assert(Builder::goes_to(r_mask, data, r_mask.len(), w,
                                r_sel.len(), selector));
                            Builder::lemma_then(r_sel, r_mask, data, r_mask.len(), w,
                                r_sel.len(), selector, 0, self.action.to_ret());
                        } else {
                            assert(r_mask == r_sel);
                        }
                        Builder::lemma_then(r_mask, r_arg, data, r_arg.len(), a, r_mask.len(), w,
                            0, self.action.to_ret());
                    }
                    assert forall |data: &[u8], a: u32|
                        Event::parse(data) is Some
                        && !self.body_holds(arch, nr, Event::of(data))
                        implies #[trigger] Builder::lands(r_arg, data, r_arg.len(), a,
                            base.len()) by {
                        Event::lemma_image(data);
                        assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * 0) as u32)
                            == (Event::of(data).args[0] & 0xFFFF_FFFF) as u32);
                        let w = Builder::word(data, Policy::OFFSET_EVENT_ARGS);
                        let selector = if is_ipc { w & 0xFFFF } else { w };
                        Self::lemma_ipc_selector(Event::of(data).args[0]);
                        assert(selector != arg);
                        assert(Builder::goes_to_all(r_arg, data, r_arg.len(),
                            (r_arg.len() - 1) as nat, w));
                        assert(Builder::goes_to(r_arg, data, r_arg.len(), a, r_mask.len(), w));
                        assert(Builder::goes_to(r_sel, data, r_sel.len(), selector,
                            end as nat, selector));
                        assert(Builder::lands(r_sel, data, r_sel.len(), selector, end as nat));
                        if is_ipc {
                            Builder::lemma_alu(r_mask, AluOp::And, 0xFFFF);
                            assert(Builder::goes_to(r_mask, data, r_mask.len(), w,
                                r_sel.len(), selector));
                            Builder::lemma_then(r_sel, r_mask, data, r_mask.len(), w,
                                r_sel.len(), selector, end as nat, w);
                        } else {
                            assert(r_mask == r_sel);
                        }
                        assert(Builder::lands(r_mask, data, r_mask.len(), w, end as nat));
                        Builder::lemma_then(r_mask, r_arg, data, r_arg.len(), a, r_mask.len(), w,
                            end as nat, w);
                    }
                }
                b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_ARGS));
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
            self.conds[i].emit(b, arch, self.syscall, sig, end)?;
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
        if arch != Arch::X86 || self.no_mux {
            None
        } else {
            let mux = if self.syscall.to_socketcall_arg() is Some {
                Some(Syscall::Socketcall)
            } else if self.syscall.to_ipc_arg() is Some {
                Some(Syscall::Ipc)
            } else {
                None
            };
            match mux {
                Some(name) => match name.spec_nr(arch) {
                    Some(nr) => Some(nr as u32),
                    None => None,
                },
                None => None,
            }
        }
    }

    /// Executable version of [`Rule::spec_mux_nr`].
    #[verifier::when_used_as_spec(spec_mux_nr)]
    pub(super) fn mux_nr(&self, arch: Arch) -> (res: Option<u32>)
        ensures res == self.spec_mux_nr(arch)
    {
        // Exact rules do not emit a multiplexed match.
        if arch != Arch::X86 || self.no_mux {
            return None;
        }
        let mux = if self.syscall.socketcall_arg().is_some() {
            Some(Syscall::Socketcall)
        } else if self.syscall.ipc_arg().is_some() {
            Some(Syscall::Ipc)
        } else {
            None
        };
        match mux {
            Some(name) => name.nr(arch).map(|nr: i32| -> (res: u32)
                ensures res == nr as u32
            { nr as u32 }),
            None => None,
        }
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
