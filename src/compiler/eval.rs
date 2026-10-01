//! What the filter computes, told as a policy-level account of its blocks and rule tests.

use vstd::prelude::*;
use crate::spec::policy::*;
#[allow(unused_imports)]
use crate::spec::expr::*;

verus! {

impl Arch {
    /// Whether the architecture guard accepts the event's token and syscall ABI.
    pub(crate) open spec fn matches_event(self, ev: Event) -> bool {
        &&& ev.arch == self.token()
        &&& self == Arch::X86_64 ==> ev.nr & 0x4000_0000 == 0 || ev.nr == -1
    }
}

impl<S: Syscall> Rule<S> {
    /// Whether the rule is evaluated on `arch`, given that the policy includes `arch`.
    pub(crate) open spec fn active_on(self, arch: Arch) -> bool {
        self.archs@.len() == 0 || self.archs@.contains(arch)
    }

    /// Whether the test for syscall number `nr` reaches this rule, and `cond` over
    /// signature `sig` then accepts `ev`.
    pub(super) open spec fn matches_at(self, arch: Arch, nr: u32, cond: Cond, sig: Seq<PrimType>, ev: Event) -> bool {
        ev.nr as u32 == nr && cond.eval(arch, sig, arch.interp_args(ev.args, sig))
    }

    /// Whether either of the tests a block emits for this rule reaches it and accepts `ev`.
    pub(super) open spec fn matches(self, arch: Arch, ev: Event) -> bool {
        ||| match self.syscall.spec_nr(arch) {
                Some(nr) => self.matches_at(arch, nr as u32, *self.cond, self.syscall.spec_signature(arch), ev),
                None => false,
            }
        ||| !self.no_mux && match self.syscall.spec_mux(arch) {
                Some((mux, cond)) => match mux.spec_nr(arch) {
                    Some(nr) => self.matches_at(arch, nr as u32, cond, mux.spec_signature(arch), ev),
                    None => false,
                },
                None => false,
            }
    }

    /// The tests a block emits for this rule come to the rule's own account of matching.
    pub(super) proof fn lemma_matches(self, arch: Arch, ev: Event)
        requires ev.args.len() == Event::ARG_COUNT_MAX, self.active_on(arch)
        ensures self.matches(arch, ev) <==> self.eval(arch, ev)
    {
        let m = ev.nr;
        assert(forall |nr: i32| #[trigger] (nr as u32) == (m as u32) ==> nr == m) by (bit_vector);
    }
}

impl<S: Syscall> Policy<S> {
    /// Whether rule `j` is included in the emitted priority buckets and rule prefix.
    pub(super) open spec fn included(self, j: int, priority: int, i: int) -> bool {
        &&& 0 <= j < self.rules@.len()
        &&& self.rules@[j].action.precedence() < priority
            || (self.rules@[j].action.precedence() == priority && j < i)
    }

    /// The highest-precedence matching rule, with later rules breaking ties.
    pub(crate) open spec fn dispatch(self, arch: Arch, ev: Event, priority: int, i: int) -> Action
        decreases priority + 1, i
    {
        if priority < 0 {
            self.act_no_match
        } else if i <= 0 {
            self.dispatch(arch, ev, priority - 1, self.rules@.len() as int)
        } else if self.rules@[i - 1].action.precedence() == priority
            && self.rules@[i - 1].eval(arch, ev) {
            self.rules@[i - 1].action
        } else {
            self.dispatch(arch, ev, priority, i - 1)
        }
    }

    /// The action the blocks for `archs[i..]` take on `ev`.
    pub(crate) open spec fn blocks(self, ev: Event, i: int) -> Action
        decreases self.archs@.len() - i
    {
        if i >= self.archs@.len() {
            self.act_bad_arch
        } else if self.archs@[i].matches_event(ev) {
            self.dispatch(self.archs@[i], ev, 7, self.rules@.len() as int)
        } else {
            self.blocks(ev, i + 1)
        }
    }

    /// Dispatch selects the greatest matching precedence and then the greatest rule index.
    pub(super) proof fn lemma_dispatch(self, arch: Arch, ev: Event, priority: int, i: int)
        requires -1 <= priority <= 7, 0 <= i <= self.rules@.len()
        ensures
            (exists |j: int| {
                &&& self.included(j, priority, i)
                &&& #[trigger] self.rules@[j].eval(arch, ev)
                &&& self.rules@[j].action == self.dispatch(arch, ev, priority, i)
                &&& forall |k: int| self.included(k, priority, i)
                    && #[trigger] self.rules@[k].eval(arch, ev) ==> {
                        &&& self.rules@[k].action.precedence() <= self.rules@[j].action.precedence()
                        &&& self.rules@[k].action.precedence() == self.rules@[j].action.precedence() ==> k <= j
                    }
            }) || (self.dispatch(arch, ev, priority, i) == self.act_no_match
                && (forall |j: int| self.included(j, priority, i)
                    ==> !#[trigger] self.rules@[j].eval(arch, ev))),
        decreases priority + 1, i
    {
        if priority >= 0 {
            if i == 0 {
                self.lemma_dispatch(arch, ev, priority - 1, self.rules@.len() as int);
            } else if self.rules@[i - 1].action.precedence() != priority
                || !self.rules@[i - 1].eval(arch, ev) {
                self.lemma_dispatch(arch, ev, priority, i - 1);
            }
        }
    }

    /// The policy accepts the action its blocks settle on.
    pub(crate) proof fn lemma_blocks(self, ev: Event, i: int)
        requires
            self.wf(),
            0 <= i <= self.archs@.len(),
            forall |j: int| 0 <= j < i ==> !(#[trigger] self.archs@[j]).matches_event(ev),
        ensures self.eval(ev, self.blocks(ev, i))
        decreases self.archs@.len() - i
    {
        if i >= self.archs@.len() {
            assert forall |a: Arch| !self.is_active_arch(a, ev) by {
                if self.is_active_arch(a, ev) {
                    let j = choose |j: int| 0 <= j < self.archs@.len() && self.archs@[j] == a;
                    assert(self.archs@[j].matches_event(ev));
                    assert(false);
                }
            }
        } else if self.archs@[i].matches_event(ev) {
            let arch = self.archs@[i];
            let act = self.dispatch(arch, ev, 7, self.rules@.len() as int);
            assert(self.archs@.contains(arch));
            assert(self.is_active_arch(arch, ev));
            self.lemma_dispatch(arch, ev, 7, self.rules@.len() as int);
            assert forall |j: int| 0 <= j < self.rules@.len() implies
                self.included(j, 7, self.rules@.len() as int) by {
                assert(self.rules@[j].action.precedence() <= 7);
            }
            if exists |j: int| 0 <= j < self.rules@.len()
                && #[trigger] self.rules@[j].eval(arch, ev)
                && self.rules@[j].action == act {
                let j = choose |j: int| {
                    &&& self.included(j, 7, self.rules@.len() as int)
                    &&& #[trigger] self.rules@[j].eval(arch, ev)
                    &&& self.rules@[j].action == act
                    &&& forall |k: int| self.included(k, 7, self.rules@.len() as int)
                        && #[trigger] self.rules@[k].eval(arch, ev) ==> {
                            &&& self.rules@[k].action.precedence() <= self.rules@[j].action.precedence()
                            &&& self.rules@[k].action.precedence() == self.rules@[j].action.precedence() ==> k <= j
                        }
                };
                assert forall |k: int| #![trigger self.rules@[k]]
                    0 <= k < self.rules@.len() && k != j && self.rules@[k].eval(arch, ev) implies {
                        ||| self.rules@[k].action.precedence() < act.precedence()
                        ||| k < j && self.rules@[k].action.precedence() == act.precedence()
                    } by {
                    assert(self.included(k, 7, self.rules@.len() as int));
                }
                assert(self.eval(ev, act));
            } else {
                assert forall |a: Arch, j: int| self.is_active_arch(a, ev)
                    && 0 <= j < self.rules@.len()
                    implies !#[trigger] self.rules@[j].eval(a, ev) by {
                    assert(a == arch);
                    assert(!self.rules@[j].eval(arch, ev));
                }
                assert(self.eval(ev, act));
            }
        } else {
            self.lemma_blocks(ev, i + 1);
        }
    }
}

} // verus!
