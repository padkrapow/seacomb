//! Compiling one architecture's block: the guard that claims an event, and the dispatch
//! of the policy's rules under it.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};
use super::CompileError;
use super::builder::{Builder, Label};
#[allow(unused_imports)]
use super::machine::Regs;

verus! {

impl Arch {
    /// Executable version of [`Arch::token`].
    fn to_token(self) -> (res: u32)
        ensures res == self.token()
    {
        match self {
            Arch::X86 => Self::TOKEN_X86,
            Arch::X86_64 => Self::TOKEN_X86_64,
            Arch::Arm => Self::TOKEN_ARM,
            Arch::Aarch64 => Self::TOKEN_AARCH64,
        }
    }

    /// Emits the architecture guard and loads the syscall number on a match.
    ///
    /// ```text
    ///     ld  [arch]
    ///     jne #token -> end
    ///     ld  [nr]
    ///     jeq #-1 -> body      (x86_64 only)
    ///     jset #0x40000000 -> end  (x86_64 only)
    /// ```
    fn emit_guard(self, b: &mut Builder, end: Label) -> (res: Result<(), CompileError>)
        requires 0 < end <= b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && self.matches_event(Event::of(data)) ==>
                #[trigger] Builder::passes(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), Event::of(data).nr as u32),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && !self.matches_event(Event::of(data)) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), r, end as nat),
    {
        let ghost body = b.rev@;
        if self == Arch::X86_64 {
            let skip = b.label();
            b.emit_jump(JmpOp::Set, Src::K(0x4000_0000), true, end)?;
            let ghost x32_guard = b.rev@;
            b.emit_jump(JmpOp::Eq, Src::K(u32::MAX), true, skip)?;
            proof {
                assert forall |data: &[u8], r: Regs|
                    #![trigger Builder::goes(b.rev@, data, b.rev@.len(), r, body.len(), r)]
                    #![trigger Builder::goes(b.rev@, data, b.rev@.len(), r, end as nat, r)]
                    r.a != u32::MAX implies Builder::goes(b.rev@, data, b.rev@.len(), r,
                        if r.a & 0x4000_0000 == 0 { body.len() } else { end as nat }, r) by {
                    let to = if r.a & 0x4000_0000 == 0 { body.len() } else { end as nat };
                    assert(Builder::goes(x32_guard, data, x32_guard.len(), r, to, r));
                    Builder::lemma_goes_trans(x32_guard, b.rev@, data, b.rev@.len(), r,
                        x32_guard.len(), r, to, r);
                }
            }
        }
        let ghost guarded_nr = b.rev@;
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_NR));
        proof { Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_NR); }
        let ghost loaded_nr = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(self.to_token()), false, end)?;
        let ghost guarded_arch = b.rev@;
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_ARCH));
        proof {
            Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_ARCH);
            assert forall |data: &[u8], r: Regs|
                #![trigger Builder::passes(b.rev@, data, b.rev@.len(), r, body.len(), Event::of(data).nr as u32)]
                #![trigger Builder::lands(b.rev@, data, b.rev@.len(), r, end as nat)]
                Event::parse(data) is Some && r.wf() implies
                if self.matches_event(Event::of(data)) {
                    Builder::passes(b.rev@, data, b.rev@.len(), r, body.len(), Event::of(data).nr as u32)
                } else {
                    Builder::lands(b.rev@, data, b.rev@.len(), r, end as nat)
                } by {
                let ev = Event::of(data);
                Event::lemma_image(data);
                let ra = Regs { a: ev.arch, ..r };
                let rn = Regs { a: ev.nr as u32, ..r };
                assert(Builder::goes(b.rev@, data, b.rev@.len(), r, guarded_arch.len(), ra));
                let to = if self.matches_event(ev) { body.len() } else { end as nat };
                if ev.arch == self.token() {
                    let nr = ev.nr;
                    assert(((nr as u32) & 0x4000_0000 == 0) <==> (nr & 0x4000_0000 == 0)) by (bit_vector);
                    assert(((nr as u32) == u32::MAX) <==> (nr == -1)) by (bit_vector);
                    assert(Builder::goes(guarded_nr, data, guarded_nr.len(), rn, to, rn));
                    assert(Builder::goes(loaded_nr, data, loaded_nr.len(), ra, guarded_nr.len(), rn));
                    Builder::lemma_goes_trans(guarded_nr, loaded_nr, data, loaded_nr.len(), ra,
                        guarded_nr.len(), rn, to, rn);
                    assert(Builder::goes(guarded_arch, data, guarded_arch.len(), ra, loaded_nr.len(), ra));
                    Builder::lemma_goes_trans(loaded_nr, guarded_arch, data, guarded_arch.len(), ra,
                        loaded_nr.len(), ra, to, rn);
                    Builder::lemma_goes_trans(guarded_arch, b.rev@, data, b.rev@.len(), r,
                        guarded_arch.len(), ra, to, rn);
                } else {
                    assert(Builder::goes(guarded_arch, data, guarded_arch.len(), ra, end as nat, ra));
                    Builder::lemma_goes_trans(guarded_arch, b.rev@, data, b.rev@.len(), r,
                        guarded_arch.len(), ra, end as nat, ra);
                }
            }
        }
        Ok(())
    }
}

impl Rule {
    /// Executable version of [`Rule::active_on`].
    fn is_active_on(&self, arch: Arch) -> (res: bool)
        ensures res == self.active_on(arch)
    {
        if self.archs.is_empty() {
            return true;
        }
        let mut i: usize = 0;
        while i < self.archs.len()
            invariant
                i <= self.archs@.len(),
                forall |k: int| 0 <= k < i ==> #[trigger] self.archs@[k] != arch,
            decreases self.archs@.len() - i
        {
            if self.archs[i] == arch {
                proof { assert(self.archs@[i as int] == arch); }
                return true;
            }
            i += 1;
        }
        false
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

impl Policy {
    /// Emits the rules and default return for an architecture token.
    ///
    /// ```text
    ///     <architecture guard> -> end
    ///     <rules by descending precedence and descending index>
    ///     ret #act_no_match
    /// end:
    /// ```
    pub(super) fn emit_arch_block(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires self.wf(), self.archs@.contains(arch), 0 < b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], tail: Action| Event::parse(data) is Some
                && #[trigger] Builder::returns_all(old(b).rev@, data, old(b).rev@.len(), tail.to_ret()) ==>
                Builder::returns_all(final(b).rev@, data, final(b).rev@.len(),
                    if arch.matches_event(Event::of(data)) {
                        self.dispatch(arch, Event::of(data), 7, self.rules@.len() as int).to_ret()
                    } else { tail.to_ret() }),
    {
        let end = b.label();
        let ghost prev = b.rev@;
        self.emit_arch(b, arch)?;
        let ghost body = b.rev@;
        arch.emit_guard(b, end)?;
        proof {
            assert forall |data: &[u8], tail: Action| Event::parse(data) is Some
                && #[trigger] Builder::returns_all(prev, data, prev.len(), tail.to_ret()) implies
                Builder::returns_all(b.rev@, data, b.rev@.len(),
                    if arch.matches_event(Event::of(data)) {
                        self.dispatch(arch, Event::of(data), 7, self.rules@.len() as int).to_ret()
                    } else { tail.to_ret() }) by {
                let ev = Event::of(data);
                let want = if arch.matches_event(ev) {
                    self.dispatch(arch, ev, 7, self.rules@.len() as int).to_ret()
                } else { tail.to_ret() };
                assert forall |r: Regs| r.wf() implies #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), r, want) by {
                    if arch.matches_event(ev) {
                        assert(Builder::passes(b.rev@, data, b.rev@.len(), r, body.len(), ev.nr as u32));
                        let t = choose |t: Regs| t.wf() && t.a == ev.nr as u32
                            && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r, body.len(), t);
                        Builder::lemma_then(body, b.rev@, data, b.rev@.len(), r, body.len(), t, 0, want);
                    } else {
                        assert(Builder::lands(b.rev@, data, b.rev@.len(), r, prev.len()));
                        let t = choose |t: Regs| t.wf()
                            && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r, prev.len(), t);
                        assert(Builder::returns(prev, data, prev.len(), t, want));
                        Builder::lemma_then(prev, b.rev@, data, b.rev@.len(), r, prev.len(), t, 0, want);
                    }
                }
            }
        }
        Ok(())
    }

    /// Emits an architecture's rules and default return in descending precedence and reverse insertion order.
    fn emit_arch(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires self.wf(), self.archs@.contains(arch), 0 < b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && r.a == Event::of(data).nr as u32 ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(), r,
                    self.dispatch(arch, Event::of(data), 7, self.rules@.len() as int).to_ret()),
    {
        b.emit(Instr::Ret(RetVal::K(self.act_no_match.exec_to_ret())));
        proof { Builder::lemma_ret(b.rev@, self.act_no_match.to_ret()); }
        // The builder runs backward: low precedence and early rules are emitted first.
        let mut priority: u8 = 0;
        proof {
            assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && r.a == Event::of(data).nr as u32 implies
                #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), r,
                    self.dispatch(arch, Event::of(data), -1, self.rules@.len() as int).to_ret()) by {
                assert(Builder::returns_all(b.rev@, data, b.rev@.len(), self.act_no_match.to_ret()));
            }
        }
        while priority < 8
            invariant
                priority <= 8,
                self.archs@.contains(arch),
                self.wf(), b.wf(), 0 < b.rev@.len(),
                Builder::extends(old(b).rev@, b.rev@),
                forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                    && r.a == Event::of(data).nr as u32 ==>
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), r,
                        self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()),
            decreases 8 - priority
        {
            let mut i: usize = 0;
            proof {
                assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                    && r.a == Event::of(data).nr as u32 implies
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), r,
                        self.dispatch(arch, Event::of(data), priority as int, 0).to_ret()) by {
                    assert(Builder::returns(b.rev@, data, b.rev@.len(), r,
                        self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()));
                }
            }
            while i < self.rules.len()
                invariant
                    priority < 8,
                    i <= self.rules@.len(),
                    self.archs@.contains(arch),
                    self.wf(), b.wf(), 0 < b.rev@.len(),
                    Builder::extends(old(b).rev@, b.rev@),
                    forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                        && r.a == Event::of(data).nr as u32 ==>
                        #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), r,
                            self.dispatch(arch, Event::of(data), priority as int, i as int).to_ret()),
                decreases self.rules@.len() - i
            {
                let ghost prev = b.rev@;
                let ghost rule = self.rules@[i as int];
                if self.rules[i].action.priority() == priority && self.rules[i].is_active_on(arch) {
                    proof {
                        assert(rule.wf(self.archs@));
                        let active = rule.active_archs(self.archs@);
                        let k = choose |k: int| 0 <= k < active.len() && active[k] == arch;
                        assert(active[k] == arch);
                    }
                    self.rules[i].emit_tests(b, arch)?;
                }
                proof {
                    assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                        && r.a == Event::of(data).nr as u32 implies
                        #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), r,
                            self.dispatch(arch, Event::of(data), priority as int, i + 1).to_ret()) by {
                        let ev = Event::of(data);
                        let nr = ev.nr as u32;
                        let want = self.dispatch(arch, ev, priority as int, i + 1).to_ret();
                        if rule.action.precedence() == priority && rule.active_on(arch) && !rule.eval(arch, ev) {
                            assert(Builder::passes(b.rev@, data, b.rev@.len(), r, prev.len(), nr));
                            let t = choose |t: Regs| t.wf() && t.a == nr
                                && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r, prev.len(), t);
                            assert(Builder::returns(prev, data, prev.len(), t,
                                self.dispatch(arch, ev, priority as int, i as int).to_ret()));
                            Builder::lemma_then(prev, b.rev@, data, b.rev@.len(), r, prev.len(), t, 0, want);
                        }
                    }
                }
                i += 1;
            }
            priority += 1;
        }
        proof {
            assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf()
                && r.a == Event::of(data).nr as u32 implies
                #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), r,
                    self.dispatch(arch, Event::of(data), 7, self.rules@.len() as int).to_ret()) by {
                assert(Builder::returns(b.rev@, data, b.rev@.len(), r,
                    self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()));
            }
        }
        Ok(())
    }
}

} // verus!
