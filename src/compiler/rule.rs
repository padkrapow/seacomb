//! Compiling one rule: the test that reaches it, and the condition under it.

use vstd::prelude::*;
use crate::spec::{policy::*, syscall::*, cbpf::*, expr::*};
use super::CompileError;
use super::builder::Builder;

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
            self.cond.wf(arch, self.syscall.spec_signature(arch)),
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
    ///     ja  <test>          ; the test starts elsewhere
    ///     <test of the condition> -> ret/end
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
            self.cond.wf(arch, self.syscall.spec_signature(arch)),
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

        let ret = b.label();
        let sig = self.syscall.signature(arch);
        let entry = self.cond.emit(b, arch, Ghost(sig@), sig, ret, end)?;
        let ghost r_cond = b.rev@;
        if entry != b.label() {
            b.emit_goto(entry)?;
        }
        proof {
            assert forall |data: &[u8], a: u32| Event::parse(data) is Some implies
                #[trigger] Builder::goes_to(b.rev@, data, b.rev@.len(), a, entry as nat, a) by {
                if entry == r_cond.len() {
                    assert(Builder::goes_to(b.rev@, data, entry as nat, a, entry as nat, a));
                }
            }
            assert forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.body_holds(arch, nr, Event::of(data))
                implies #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), a,
                    self.action.to_ret()) by {
                assert(self.cond.holds(arch, sig@, data));
                assert(Builder::lands(r_cond, data, entry as nat, a, ret as nat));
                let m = choose |m: u32| Builder::goes_to(r_cond, data, entry as nat, a, ret as nat, m);
                assert(Builder::returns(r_ret, data, ret as nat, m, self.action.to_ret()));
                Builder::lemma_then(r_ret, r_cond, data, entry as nat, a, ret as nat, m, 0,
                    self.action.to_ret());
                Builder::lemma_then(r_cond, b.rev@, data, b.rev@.len(), a, entry as nat, a, 0,
                    self.action.to_ret());
            }
            assert forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.body_holds(arch, nr, Event::of(data))
                implies #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), a, end as nat) by {
                assert(!self.cond.holds(arch, sig@, data));
                assert(Builder::lands(r_cond, data, entry as nat, a, end as nat));
                Builder::lemma_then(r_cond, b.rev@, data, b.rev@.len(), a, entry as nat, a,
                    end as nat, 0);
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
            self.cond.wf(arch, self.syscall.spec_signature(arch)),
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
