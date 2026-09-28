//! Compiling one rule: the test that reaches it, and the condition under it.

use vstd::prelude::*;
use crate::spec::{policy::*, syscall::*, cbpf::*, expr::*};
use super::CompileError;
use super::builder::Builder;
#[allow(unused_imports)]
use super::machine::Regs;

verus! {

impl Arch {
    /// Whether an argument of type `ty` takes two slots.
    pub(super) open spec fn splits(self, ty: PrimType) -> bool {
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

    /// The bits of the arguments of a syscall with signature `sig`, read from `slot` on.
    spec fn interp_from(self, args: Seq<u64>, sig: Seq<PrimType>, slot: nat) -> Seq<u64> {
        match self {
            Arch::X86 => Self::interp_args_x86(args.skip(slot as int), sig),
            Arch::Arm => Self::interp_args_arm(args, sig, slot as int),
            _ => Seq::new(sig.len(), |i: int| args[slot + i]),
        }
    }

    /// The bits of an argument of type `ty` that starts at `slot`.
    pub(super) open spec fn raw(self, args: Seq<u64>, ty: PrimType, slot: nat) -> u64 {
        if self.splits(ty) {
            (args[slot as int] & 0xFFFF_FFFFu64) | ((args[slot + 1 as int] & 0xFFFF_FFFFu64) << 32u64)
        } else {
            args[slot as int]
        }
    }

    /// Whether argument `n` of a syscall with signature `sig` starts at `slot`.
    pub(super) open spec fn arg_at(self, sig: Seq<PrimType>, n: nat, slot: nat) -> bool {
        forall |args: Seq<u64>| args.len() == Rule::ARG_COUNT_MAX ==>
            #[trigger] self.interp_args(args, sig)[n as int] == self.raw(args, sig[n as int], slot)
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
        ensures self.interp_from(args, sig, slot)[0] == self.raw(args, sig[0],
            if self == Arch::Arm && self.splits(sig[0]) { slot + slot % 2 } else { slot })
    {
        if self == Arch::X86 {
            assert(args.skip(slot as int)[0] == args[slot as int]);
            if self.splits(sig[0]) {
                assert(args.skip(slot as int)[1] == args[slot + 1 as int]);
            }
        }
    }

    /// The low and high words of the bits of a 64-bit argument that starts at `slot`.
    pub(super) proof fn lemma_raw_words(self, args: Seq<u64>, ty: PrimType, slot: nat)
        requires slot < args.len(), self.splits(ty) ==> slot + 1 < args.len()
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
    pub(super) fn arg_slot(self, sig: &[PrimType], n: usize) -> (res: Result<u32, CompileError>)
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
                    == self.raw(args, sig@[n as int], slot as nat) by {
                self.lemma_from_first(args, rest, unaligned as nat);
            }
        }
        Ok(slot)
    }

    /// Executable version of [`Arch::splits`].
    pub(super) fn exec_splits(self, ty: PrimType) -> (res: bool)
        ensures res == self.splits(ty)
    {
        (self == Arch::X86 || self == Arch::Arm) && ty.exec_bits(self) == 64
    }
}

impl Rule {
    /// Number of argument slots in `seccomp_data`.
    pub const ARG_COUNT_MAX: u32 = 6;
}

impl Rule {
    /// Emits the test that reaches this rule at syscall number `nr`, and the rule's
    /// body under it, with multiplexer selector and mask `sel`.
    ///
    /// Forward layout, entered with `A` holding `seccomp_data.nr`:
    ///
    /// ```text
    ///     jne #nr -> end
    ///     <body>
    ///     ld  [nr]            ; hands A back to the test behind this one
    /// end:
    /// ```
    fn emit(&self, b: &mut Builder, arch: Arch, nr: u32, sel: Option<(u32, u32)>) -> (res: Result<(), CompileError>)
        requires
            self.cond.wf(arch, self.syscall.spec_signature(arch)),
            0 < b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && r.a == Event::of(data).nr as u32 && self.matches_at(arch, nr, sel, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(), r, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && r.a == Event::of(data).nr as u32 && !self.matches_at(arch, nr, sel, Event::of(data)) ==>
                #[trigger] Builder::passes(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), Event::of(data).nr as u32),
    {
        let end = b.label();
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_NR));
        proof { Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_NR); }
        let ghost r_nr = b.rev@;
        self.emit_body(b, arch, sel)?;
        let ghost r_body = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(nr), false, end)?;
        proof {
            assert forall |data: &[u8], r: Regs|
                #![trigger Builder::returns(b.rev@, data, b.rev@.len(), r, self.action.to_ret())]
                #![trigger Builder::passes(b.rev@, data, b.rev@.len(), r, end as nat, Event::of(data).nr as u32)]
                Event::parse(data) is Some && r.wf() && r.a == Event::of(data).nr as u32 implies
                if self.matches_at(arch, nr, sel, Event::of(data)) {
                    Builder::returns(b.rev@, data, b.rev@.len(), r, self.action.to_ret())
                } else {
                    Builder::passes(b.rev@, data, b.rev@.len(), r, end as nat, Event::of(data).nr as u32)
                } by {
                let ev = Event::of(data);
                Event::lemma_image(data);
                if ev.nr as u32 == nr {
                    assert(Builder::goes(b.rev@, data, b.rev@.len(), r, r_body.len(), r));
                    if self.body_holds(arch, sel, ev) {
                        Builder::lemma_then(r_body, b.rev@, data, b.rev@.len(), r, r_body.len(), r,
                            0, self.action.to_ret());
                    } else {
                        assert(Builder::lands(r_body, data, r_body.len(), r, r_nr.len()));
                        let t = choose |t: Regs| t.wf()
                            && #[trigger] Builder::goes(r_body, data, r_body.len(), r, r_nr.len(), t);
                        assert(Builder::goes(r_nr, data, r_nr.len(), t, end as nat, Regs { a: ev.nr as u32, ..t }));
                        Builder::lemma_then(r_nr, r_body, data, r_body.len(), r, r_nr.len(), t,
                            end as nat, ev.nr as u32);
                        Builder::lemma_then(r_body, b.rev@, data, b.rev@.len(), r, r_body.len(), r,
                            end as nat, ev.nr as u32);
                    }
                } else {
                    assert(Builder::goes(b.rev@, data, b.rev@.len(), r, end as nat, r));
                }
            }
        }
        Ok(())
    }

    /// Emits whatever this rule tests beyond the syscall number, then its action: the
    /// multiplexer selector and mask `sel` if there are any, and the condition otherwise.
    ///
    /// Forward layout, with `end` just past the body:
    ///
    /// ```text
    ///     ja  <test>          ; the test starts elsewhere
    ///     <test of the condition> -> ret/end
    ///     ret #action
    /// end:
    /// ```
    /// With a selector, it is the only test:
    /// ```text
    ///     ld  [arg 0]
    ///     and #mask           ; mask != 0xffffffff
    ///     jne #selector -> end
    ///     ret #action
    /// end:
    /// ```
    fn emit_body(&self, b: &mut Builder, arch: Arch, sel: Option<(u32, u32)>) -> (res: Result<(), CompileError>)
        requires
            self.cond.wf(arch, self.syscall.spec_signature(arch)),
            0 < b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && self.body_holds(arch, sel, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(), r, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && !self.body_holds(arch, sel, Event::of(data)) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), r, old(b).rev@.len()),
    {
        let end = b.label();
        let ghost base = b.rev@;
        b.emit(Instr::Ret(RetVal::K(self.action.exec_to_ret())));
        let ghost r_ret = b.rev@;
        proof {
            Builder::lemma_ret(r_ret, self.action.to_ret());
            assert forall |data: &[u8], r: Regs| r.wf() implies #[trigger] Builder::returns(r_ret, data,
                r_ret.len(), r, self.action.to_ret()) by {
                assert(Builder::returns_all(r_ret, data, r_ret.len(), self.action.to_ret()));
            }
        }

        if let Some((arg, mask)) = sel {
            b.emit_jump(JmpOp::Eq, Src::K(arg), false, end)?;
            let ghost r_sel = b.rev@;
            b.emit_load(Policy::OFFSET_EVENT_ARGS, mask, 0);
            proof {
                assert forall |data: &[u8], r: Regs|
                    #![trigger Builder::returns(b.rev@, data, b.rev@.len(), r, self.action.to_ret())]
                    #![trigger Builder::lands(b.rev@, data, b.rev@.len(), r, base.len())]
                    Event::parse(data) is Some && r.wf() implies
                    if self.body_holds(arch, sel, Event::of(data)) {
                        Builder::returns(b.rev@, data, b.rev@.len(), r, self.action.to_ret())
                    } else {
                        Builder::lands(b.rev@, data, b.rev@.len(), r, base.len())
                    } by {
                    let arg0 = Event::of(data).args[0];
                    let w = Builder::word(data, Policy::OFFSET_EVENT_ARGS);
                    Event::lemma_image(data);
                    assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * 0) as u32)
                        == (arg0 & 0xFFFF_FFFF) as u32);
                    assert((arg0 & (mask as u64)) as u32 == ((arg0 & 0xFFFF_FFFF) as u32) & mask)
                        by (bit_vector);
                    assert((w & mask) ^ 0u32 == w & mask) by (bit_vector);
                    let got = Regs { a: (w & mask) ^ 0, ..r };
                    assert(self.body_holds(arch, sel, Event::of(data)) <==> got.a == arg);
                    let to = if got.a == arg { r_ret.len() } else { end as nat };
                    assert(Builder::goes(r_sel, data, r_sel.len(), got, to, got));
                    Builder::lemma_goes_trans(r_sel, b.rev@, data, b.rev@.len(), r, r_sel.len(), got, to, got);
                    if got.a == arg {
                        Builder::lemma_then(r_ret, b.rev@, data, b.rev@.len(), r, r_ret.len(), got,
                            0, self.action.to_ret());
                    }
                }
            }
            return Ok(());
        }

        let ret = b.label();
        let sig = self.syscall.signature(arch);
        let entry = self.cond.emit(b, arch, Ghost(sig@), sig, ret, end)?;
        let ghost r_cond = b.rev@;
        if entry != b.label() {
            b.emit_goto(entry)?;
        }
        proof {
            assert forall |data: &[u8], r: Regs|
                #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r, entry as nat, r) by {
                if entry == r_cond.len() {
                    assert(Builder::goes(b.rev@, data, entry as nat, r, entry as nat, r));
                }
            }
            assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && self.body_holds(arch, sel, Event::of(data))
                implies #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), r, self.action.to_ret()) by {
                assert(self.cond.holds(arch, sig@, data));
                assert(Builder::lands(r_cond, data, entry as nat, r, ret as nat));
                let m = choose |m: Regs| m.wf()
                    && #[trigger] Builder::goes(r_cond, data, entry as nat, r, ret as nat, m);
                Builder::lemma_then(r_ret, r_cond, data, entry as nat, r, ret as nat, m, 0,
                    self.action.to_ret());
                assert(Builder::goes(b.rev@, data, b.rev@.len(), r, entry as nat, r));
                Builder::lemma_then(r_cond, b.rev@, data, b.rev@.len(), r, entry as nat, r, 0,
                    self.action.to_ret());
            }
            assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && !self.body_holds(arch, sel, Event::of(data))
                implies #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), r, end as nat) by {
                assert(!self.cond.holds(arch, sig@, data));
                assert(Builder::lands(r_cond, data, entry as nat, r, end as nat));
                assert(Builder::goes(b.rev@, data, b.rev@.len(), r, entry as nat, r));
                Builder::lemma_then(r_cond, b.rev@, data, b.rev@.len(), r, entry as nat, r,
                    end as nat, 0);
            }
        }
        Ok(())
    }

    /// The x86 multiplexer that also reaches this rule, if one does: its syscall number,
    /// the call number it selects this rule's syscall on, and the mask it reads that with.
    pub(super) open spec fn spec_mux(&self, arch: Arch) -> Option<(u32, u32, u32)> {
        let sel = match self.syscall.to_socketcall_arg() {
            Some(arg) => Some((Syscall::Socketcall, arg, u32::MAX)),
            None => match self.syscall.to_ipc_arg() {
                Some(arg) => Some((Syscall::Ipc, arg, 0xFFFFu32)),
                None => None,
            },
        };
        match sel {
            Some((mux, arg, mask)) if arch == Arch::X86 && !self.no_mux => match mux.spec_nr(arch) {
                Some(nr) => Some((nr as u32, arg as u32, mask)),
                None => None,
            },
            _ => None,
        }
    }

    /// Executable version of [`Rule::spec_mux`].
    fn mux(&self, arch: Arch) -> (res: Option<(u32, u32, u32)>)
        ensures res == self.spec_mux(arch)
    {
        if arch != Arch::X86 || self.no_mux {
            return None;
        }
        let (mux, arg, mask) = match self.syscall.socketcall_arg() {
            Some(arg) => (Syscall::Socketcall, arg, u32::MAX),
            None => (Syscall::Ipc, self.syscall.ipc_arg()?, 0xFFFF),
        };
        mux.nr(arch).map(|nr: i32| -> (res: (u32, u32, u32))
            ensures res == (nr as u32, arg as u32, mask)
        { (nr as u32, arg as u32, mask) })
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
            self.cond.wf(arch, self.syscall.spec_signature(arch)),
            0 < b.rev@.len(), b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && r.a == Event::of(data).nr as u32 && self.eval(arch, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(), r, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && r.a == Event::of(data).nr as u32 && !self.eval(arch, Event::of(data)) ==>
                #[trigger] Builder::passes(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), Event::of(data).nr as u32),
    {
        let ghost prev = b.rev@;
        if let Some((nr, arg, mask)) = self.mux(arch) {
            self.emit(b, arch, nr, Some((arg, mask)))?;
        }
        let ghost mux = b.rev@;
        if let Some(nr) = self.syscall.bpf_nr(arch) {
            self.emit(b, arch, nr, None)?;
        }
        proof {
            assert forall |data: &[u8], r: Regs|
                #![trigger Builder::returns(b.rev@, data, b.rev@.len(), r, self.action.to_ret())]
                #![trigger Builder::passes(b.rev@, data, b.rev@.len(), r, prev.len(), Event::of(data).nr as u32)]
                Event::parse(data) is Some && r.wf() && r.a == Event::of(data).nr as u32 implies
                if self.eval(arch, Event::of(data)) {
                    Builder::returns(b.rev@, data, b.rev@.len(), r, self.action.to_ret())
                } else {
                    Builder::passes(b.rev@, data, b.rev@.len(), r, prev.len(), Event::of(data).nr as u32)
                } by {
                let ev = Event::of(data);
                let nr = ev.nr as u32;
                Event::lemma_image(data);
                self.lemma_matches(arch, ev);
                let own = match self.syscall.spec_bpf_nr(arch) {
                    Some(n) => self.matches_at(arch, n, None, ev),
                    None => false,
                };
                if !own {
                    assert(Builder::goes(b.rev@, data, b.rev@.len(), r, b.rev@.len(), r));
                    assert(Builder::passes(b.rev@, data, b.rev@.len(), r, mux.len(), nr));
                    let t = choose |t: Regs| t.wf() && t.a == nr
                        && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r, mux.len(), t);
                    assert(Builder::goes(mux, data, mux.len(), t, mux.len(), t));
                    if self.eval(arch, ev) {
                        assert(Builder::returns(mux, data, mux.len(), t, self.action.to_ret()));
                        Builder::lemma_then(mux, b.rev@, data, b.rev@.len(), r, mux.len(), t,
                            0, self.action.to_ret());
                    } else {
                        assert(Builder::passes(mux, data, mux.len(), t, prev.len(), nr));
                        Builder::lemma_then(mux, b.rev@, data, b.rev@.len(), r, mux.len(), t,
                            prev.len(), nr);
                    }
                }
            }
        }
        Ok(())
    }
}

} // verus!
