//! Supporting definitions and proofs for policy evaluation.

use vstd::prelude::*;
use crate::spec::policy::*;

verus! {

impl<S: Syscall> Policy<S> {
    /// Every event has an action accepted by a well-formed policy.
    pub(super) proof fn lemma_eval_total(self)
        requires self.wf()
        ensures forall |ev: Event| #[trigger] self.eval_defined(ev)
    {
        assert forall |ev: Event| #[trigger] self.eval_defined(ev) by {
            self.lemma_blocks(ev, 0);
            assert(self.eval(ev, self.blocks(ev, 0)));
        }
    }

    /// Whether this rule is the ordered match selected for the event.
    spec fn wins(self, ev: Event, a: Arch, i: int) -> bool {
        &&& self.is_active_arch(a, ev)
        &&& 0 <= i < self.rules@.len()
        &&& self.rules@[i].eval(a, ev)
        &&& forall |j: int| #![trigger self.rules@[j]]
            0 <= j < self.rules@.len() && j != i && self.rules@[j].eval(a, ev) ==> {
                ||| self.rules@[j].action.precedence() < self.rules@[i].action.precedence()
                ||| j < i && self.rules@[j].action.precedence() == self.rules@[i].action.precedence()
            }
    }

    /// An accepted action has a winning rule whenever any active rule matches.
    proof fn lemma_eval_witness(self, ev: Event, act: Action, a: Arch, i: int)
        requires
            self.wf(), self.eval(ev, act),
            self.is_active_arch(a, ev), 0 <= i < self.rules@.len(), self.rules@[i].eval(a, ev),
        ensures exists |b: Arch, j: int| #[trigger] self.wins(ev, b, j) && self.rules@[j].action == act
    {
        let (b, j) = choose |b: Arch, j: int| {
            &&& self.is_active_arch(b, ev)
            &&& 0 <= j < self.rules@.len()
            &&& #[trigger] self.rules@[j].eval(b, ev)
            &&& self.rules@[j].action == act
            &&& forall |k: int| #![trigger self.rules@[k]]
                0 <= k < self.rules@.len() && k != j && self.rules@[k].eval(b, ev) ==> {
                    ||| self.rules@[k].action.precedence() < act.precedence()
                    ||| k < j && self.rules@[k].action.precedence() == act.precedence()
                }
        };
        assert(self.wins(ev, b, j));
    }

    /// Two accepted actions for an event are equal.
    pub(super) proof fn lemma_eval_unique(self, ev: Event, act1: Action, act2: Action)
        requires self.wf(), self.eval(ev, act1), self.eval(ev, act2)
        ensures act1 == act2
    {
        if exists |a: Arch, i: int| self.is_active_arch(a, ev)
            && 0 <= i < self.rules@.len() && #[trigger] self.rules@[i].eval(a, ev) {
            let (a, i) = choose |a: Arch, i: int| self.is_active_arch(a, ev)
                && 0 <= i < self.rules@.len() && #[trigger] self.rules@[i].eval(a, ev);
            self.lemma_eval_witness(ev, act1, a, i);
            self.lemma_eval_witness(ev, act2, a, i);
            let (a, i) = choose |a: Arch, i: int| #[trigger] self.wins(ev, a, i) && self.rules@[i].action == act1;
            let (b, j) = choose |b: Arch, j: int| #[trigger] self.wins(ev, b, j) && self.rules@[j].action == act2;
            assert(a == b);
            assert(i == j);
        }
    }
}

} // verus!
