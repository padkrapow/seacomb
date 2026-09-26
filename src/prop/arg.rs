//! Supporting facts about argument conditions.

use vstd::prelude::*;
use crate::spec::policy::*;

verus! {

impl ArgCmp {
    /// A condition well-formed on a 32-bit and a 64-bit arch agrees on them.
    pub(super) proof fn lemma_eval_narrow_wide(
        self, syscall: crate::spec::syscall::Syscall,
        n: Arch, args_n: Seq<u64>,
        w: Arch, args_w: Seq<u64>,
    )
        requires
            self.wf(n, syscall),
            self.wf(w, syscall),
            syscall.spec_signature(n)[self.arg as int] == syscall.spec_signature(w)[self.arg as int],
            n.interp_args(args_n, syscall.spec_signature(n))[self.arg as int]
                == w.interp_args(args_w, syscall.spec_signature(w))[self.arg as int],
            syscall.spec_signature(n)[self.arg as int].bits(n) == 32,
            syscall.spec_signature(n)[self.arg as int].bits(w) == 64,
        ensures self.eval(n, syscall, args_n) == self.eval(w, syscall, args_w),
    {
        let ty = syscall.spec_signature(n)[self.arg as int];
        let a = self.a;
        assert(1u64 << 32u64 == 0x1_0000_0000u64) by (bit_vector);
        assert(ty.mask(n) == 0xFFFF_FFFFu64);
        assert(ty.mask(w) == u64::MAX);
        assert(0xFFFF_FFFFu64 >> 1u64 == 0x7FFF_FFFFu64) by (bit_vector);
        assert(u64::MAX >> 1u64 == 0x7FFF_FFFF_FFFF_FFFFu64) by (bit_vector);

        if self.op is MaskedEq {
            let x = n.interp_args(args_n, syscall.spec_signature(n))[self.arg as int];
            let y = (x % 0x1_0000_0000_0000_0000int) as u64;
            assert(a & !0xFFFF_FFFFu64 == 0);
            vstd::arithmetic::div_mod::lemma_mod_mod(x, 0x1_0000_0000int, 0x1_0000_0000int);
            assert(y & 0xFFFF_FFFFu64 == y % 0x1_0000_0000u64) by (bit_vector);
            assert((y & 0xFFFF_FFFFu64) & a == y & a) by (bit_vector)
                requires a & !0xFFFF_FFFFu64 == 0;
        } else if ty.signed() {
            assert(!(0xFFFF_FFFFu64 >> 1u64) == !0x7FFF_FFFFu64);
            assert(a & !0x7FFF_FFFFu64 == 0 ==> a & 0xFFFF_FFFFu64 == a && a <= 0x7FFF_FFFFu64)
                by (bit_vector);
            assert(a & !0x7FFF_FFFFu64 == !0x7FFF_FFFFu64 ==> {
                &&& a & 0xFFFF_FFFFu64 > 0x7FFF_FFFFu64
                &&& a > 0x7FFF_FFFF_FFFF_FFFFu64
                &&& (a & 0xFFFF_FFFFu64) + 0xFFFF_FFFF_0000_0000u64 == a
            }) by (bit_vector);
            assert(a & u64::MAX == a) by (bit_vector);
            assert(ty.cast(n, a) == ty.cast(w, a));
        } else {
            assert(a & !0xFFFF_FFFFu64 == 0);
            assert(a & 0xFFFF_FFFFu64 == a) by (bit_vector)
                requires a & !0xFFFF_FFFFu64 == 0;
            assert(a & u64::MAX == a) by (bit_vector);
            assert(ty.cast(n, a) == ty.cast(w, a));
        }
    }
}

} // verus!
