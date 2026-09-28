//! Top-level theorems about the semantics of policies and cBPF.

use vstd::prelude::*;
use crate::spec::cbpf::*;
use crate::spec::policy::*;

mod action;
mod chain;
mod policy;

verus! {

impl Policy {
    /// Whether this policy accepts an action for the event.
    /// Defined separately to be used as triggers.
    pub closed spec fn eval_defined(self, ev: Event) -> bool {
        exists |act: Action| self.eval(ev, act)
    }

    /// Compiling each policy preserves the chain's action, including data and tie-breaking.
    /// The per-pair premise is the successful `Policy::to_cbpf` postcondition.
    pub proof fn theorem_eval_chain_compiled(
        policies: Seq<Policy>, filters: Seq<Program>,
        data: &[u8], ev: Event,
    )
        requires
            policies.len() == filters.len(),
            Event::parse(data) == Some(ev),
            forall |i: int| 0 <= i < policies.len() ==> #[trigger] policies[i].wf(),
            // Each pair of policy and filter program are equivalent.
            forall |i: int| #![trigger filters[i]] 0 <= i < filters.len() ==> {
                &&& filters[i].wf()
                &&& forall |input: &[u8]| #[trigger] Event::parse(input) matches Some(ev) ==>
                    exists |act: Action| {
                        &&& #[trigger] policies[i].eval(ev, act)
                        &&& filters[i].eval(input) == Outcome::Return(act.to_ret())
                    }
            },
        ensures forall |act: Action|
            #[trigger] Self::eval_chain(policies, ev, act) == Program::eval_chain(filters, data, act.to_ret()),
    {
        hide(Policy::eval);
        hide(Program::eval);
        let actions = Seq::new(policies.len(), |i: int|
            choose |act: Action| {
                &&& #[trigger] policies[i].eval(ev, act)
                &&& filters[i].eval(data) == Outcome::Return(act.to_ret())
            });
        assert forall |i: int| 0 <= i < filters.len() implies {
            &&& policies[i].eval(ev, #[trigger] actions[i])
            &&& filters[i].eval(data) == Outcome::Return(actions[i].to_ret())
        } by {
            assert(exists |act: Action| {
                &&& #[trigger] policies[i].eval(ev, act)
                &&& filters[i].eval(data) == Outcome::Return(act.to_ret())
            });
        }
        assert forall |act: Action|
            #[trigger] Self::eval_chain(policies, ev, act)
                <==> Program::eval_chain(filters, data, act.to_ret()) by {
            Self::lemma_eval_chain_compiled_at(policies, filters, actions, ev, data, act);
        }
    }

    /// Although defined as a relation, the evaluation of a policy is a function of the event.
    pub proof fn theorem_eval_functional(self)
        requires self.wf()
        ensures
            forall |ev: Event, act1: Action, act2: Action| self.eval(ev, act1) && self.eval(ev, act2) ==> act1 == act2,
            forall |ev: Event| #[trigger] self.eval_defined(ev),
    {
        self.lemma_eval_total();
        assert forall |ev: Event, act1: Action, act2: Action|
            self.eval(ev, act1) && self.eval(ev, act2) implies act1 == act2 by {
            self.lemma_eval_unique(ev, act1, act2);
        }
    }

    /// A chain of well-formed policies admits at most one action for a given event.
    pub proof fn theorem_eval_chain_functional(policies: Seq<Policy>, ev: Event)
        requires forall |i: int| 0 <= i < policies.len() ==> #[trigger] policies[i].wf()
        ensures forall |a: Action, b: Action|
            Self::eval_chain(policies, ev, a) && Self::eval_chain(policies, ev, b) ==> a == b
    {
        hide(Policy::eval);
        assert forall |a: Action, b: Action|
            Self::eval_chain(policies, ev, a) && Self::eval_chain(policies, ev, b) implies a == b by {
            if policies.len() != 0 {
                Self::lemma_chain_eval_witness(policies, ev, a);
                Self::lemma_chain_eval_witness(policies, ev, b);
                let i = choose |i: int| #[trigger] Self::chain_wins(policies, ev, a, i);
                let j = choose |j: int| #[trigger] Self::chain_wins(policies, ev, b, j);
                assert(i == j);
                policies[i].lemma_eval_unique(ev, a, b);
            }
        }
    }
}

impl Program {
    /// A filter chain admits at most one raw return value for a given input (i.e., a partial function).
    pub proof fn theorem_eval_chain_unique(filters: Seq<Program>, data: &[u8])
        ensures forall |a: u32, b: u32|
            Self::eval_chain(filters, data, a) && Self::eval_chain(filters, data, b) ==> a == b
    {
        hide(Program::eval);
        assert forall |a: u32, b: u32|
            Self::eval_chain(filters, data, a) && Self::eval_chain(filters, data, b) implies a == b by {
            if a != Action::RET_ALLOW {
                let i = choose |i: int| #[trigger] Self::chain_wins(filters, data, a, i);
                if b != Action::RET_ALLOW {
                    let j = choose |j: int| #[trigger] Self::chain_wins(filters, data, b, j);
                    assert(i == j);
                } else {
                    assert((a & Action::RET_ACTION) == Action::RET_ALLOW);
                }
            } else if b != Action::RET_ALLOW {
                let j = choose |j: int| #[trigger] Self::chain_wins(filters, data, b, j);
                assert((b & Action::RET_ACTION) == Action::RET_ALLOW);
            }
        }
    }
}

} // verus!
