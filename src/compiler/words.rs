//! The 32-bit words a filter compares, and the `seccomp_data` image they come from.

use vstd::prelude::*;
#[allow(unused_imports)]
use crate::spec::{policy::*, cbpf::*};
#[allow(unused_imports)]
use super::builder::Builder;

verus! {

impl Policy {
    /// Byte offset of `seccomp_data.nr`.
    pub(super) const OFFSET_EVENT_NR: u32 = 0;

    /// Byte offset of `seccomp_data.arch`.
    pub(super) const OFFSET_EVENT_ARCH: u32 = 4;

    /// Byte offset of the low half of `seccomp_data.args[0]`.
    pub(super) const OFFSET_EVENT_ARGS: u32 = 16;
}

impl Event {
    /// The event the 64-byte image `data` describes.
    pub(super) open spec fn of(data: &[u8]) -> Event {
        Event::parse(data)->Some_0
    }

    /// The filter's loads read back the fields of a successfully parsed event.
    pub(super) proof fn lemma_image(data: &[u8])
        requires Event::parse(data) is Some
        ensures
            Self::of(data).args.len() == Rule::ARG_COUNT_MAX,
            Builder::word(data, Policy::OFFSET_EVENT_NR) == Self::of(data).nr as u32,
            Builder::word(data, Policy::OFFSET_EVENT_ARCH) == Self::of(data).arch,
            forall |k: u32| k < Rule::ARG_COUNT_MAX ==>
                #[trigger] Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * k) as u32)
                    == (Self::of(data).args[k as int] & 0xFFFF_FFFF) as u32,
            forall |k: u32| k < Rule::ARG_COUNT_MAX ==>
                #[trigger] Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * k + 4) as u32)
                    == (Self::of(data).args[k as int] >> 32) as u32,
    {
        let ev = Self::of(data);
        // `nr` is the word at offset 0, put through the `i32` round trip `parse` writes.
        let w = Builder::word(data, Policy::OFFSET_EVENT_NR);
        assert((w as i32) as u32 == w) by (bit_vector);
        // Each argument spans two words: the low one at `16 + 8 * k`, the high one four on.
        assert forall |k: u32|
            #![trigger Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * k) as u32)]
            #![trigger Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * k + 4) as u32)]
            k < Rule::ARG_COUNT_MAX implies
            Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * k) as u32)
                == (ev.args[k as int] & 0xFFFF_FFFF) as u32
            && Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * k + 4) as u32)
                == (ev.args[k as int] >> 32) as u32
        by {
            let i = Policy::OFFSET_EVENT_ARGS + 8 * (k as int);
            let c0 = data@[i];
            let c1 = data@[i + 1];
            let c2 = data@[i + 2];
            let c3 = data@[i + 3];
            let c4 = data@[i + 4];
            let c5 = data@[i + 5];
            let c6 = data@[i + 6];
            let c7 = data@[i + 7];
            assert((((c0 as u64) | ((c1 as u64) << 8) | ((c2 as u64) << 16) | ((c3 as u64) << 24)
                | ((c4 as u64) << 32) | ((c5 as u64) << 40) | ((c6 as u64) << 48)
                | ((c7 as u64) << 56)) & 0xFFFF_FFFF) as u32
                == (c0 as u32) | ((c1 as u32) << 8) | ((c2 as u32) << 16) | ((c3 as u32) << 24))
                by (bit_vector);
            assert((((c0 as u64) | ((c1 as u64) << 8) | ((c2 as u64) << 16) | ((c3 as u64) << 24)
                | ((c4 as u64) << 32) | ((c5 as u64) << 40) | ((c6 as u64) << 48)
                | ((c7 as u64) << 56)) >> 32) as u32
                == (c4 as u32) | ((c5 as u32) << 8) | ((c6 as u32) << 16) | ((c7 as u32) << 24))
                by (bit_vector);
        }
    }
}

} // verus!
