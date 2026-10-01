//! Verified policy optimizer.

use vstd::prelude::*;
use crate::spec::policy::*;

mod equiv;
mod fold;
mod rule;

verus! {

impl<S: Syscall> Policy<S> {
    /// Performs policy-level optimizations such as merging rules and simplifying rule conditions.
    pub(crate) fn optimize(&self) -> (opt: Policy<S>)
        requires self.wf()
        ensures
            // Optimized policy is well-formed,
            opt.wf(),
            // and equivalent to the original policy.
            forall |ev: Event, act: Action| self.eval(ev, act) <==> opt.eval(ev, act),
    {
        let mut rules: Vec<Rule<S>> = Vec::new();
        let mut k: usize = 0;
        proof { assert(self.rules@.take(0) =~= rules@); }
        while k < self.rules.len()
            invariant
                self.wf(),
                k <= self.rules@.len(),
                forall |i: int| 0 <= i < rules@.len() ==> #[trigger] rules@[i].wf(self.archs@),
                Rule::same_matches(rules@, self.rules@.take(k as int), self.archs@),
            decreases self.rules@.len() - k
        {
            let ghost done = self.rules@.take(k as int);
            let ghost next = self.rules@[k as int];
            let ghost prev = rules@;
            proof { assert(self.rules@.take(k + 1) =~= done.push(next)); }
            if let Some(rule) = self.rules[k].rewrite(self.archs.as_slice()) {
                match rule.find_merge(rules.as_slice(), self.archs.as_slice()) {
                    Some(j) => {
                        let merged = rules[j].merge(&rule, Ghost(self.archs@));
                        let ghost m = merged;
                        rules.set(j, merged);
                        proof {
                            assert forall |a: Arch, ev: Event| self.archs@.contains(a) implies
                                #[trigger] m.eval(a, ev) == (prev[j as int].eval(a, ev) || next.eval(a, ev)) by {
                                assert(rule.eval(a, ev) == next.eval(a, ev));
                            }
                            Rule::lemma_same_matches_merge(prev, done, self.archs@, j as int, m, next);
                        }
                    }
                    None => {
                        let ghost r = rule;
                        rules.push(rule);
                        proof { Rule::lemma_same_matches_push(prev, done, self.archs@, r, next); }
                    }
                }
            } else {
                proof { Rule::lemma_same_matches_skip(prev, done, self.archs@, next); }
            }
            k += 1;
        }
        let opt = Policy {
            archs: vstd::slice::slice_to_vec(self.archs.as_slice()),
            rules,
            act_no_match: self.act_no_match,
            act_bad_arch: self.act_bad_arch,
        };
        proof {
            assert(self.rules@.take(self.rules@.len() as int) =~= self.rules@);
            opt.lemma_same_eval(*self);
        }
        opt
    }
}

} // verus!
