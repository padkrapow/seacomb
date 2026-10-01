//! Rule sequences that take the same last matches, and the policies that agree because of it.

use vstd::prelude::*;
use crate::spec::policy::*;

verus! {

impl<S: Syscall> Rule<S> {
    /// The action of the last rule in `rules` of precedence `p` that matches `ev` on `arch`.
    pub(super) open spec fn last_match(rules: Seq<Rule<S>>, arch: Arch, ev: Event, p: nat) -> Option<Action>
        decreases rules.len()
    {
        if rules.len() == 0 {
            None
        } else if rules.last().action.precedence() == p && rules.last().eval(arch, ev) {
            Some(rules.last().action)
        } else {
            Self::last_match(rules.drop_last(), arch, ev, p)
        }
    }

    /// Whether `rules` and `other` take the same last match at every precedence on each of `archs`.
    pub(super) open spec fn same_matches(rules: Seq<Rule<S>>, other: Seq<Rule<S>>, archs: Seq<Arch>) -> bool {
        forall |arch: Arch, ev: Event, p: nat| archs.contains(arch) ==>
            #[trigger] Self::last_match(rules, arch, ev, p) == Self::last_match(other, arch, ev, p)
    }

    /// A rule of precedence `p` that matches `ev` on `arch` gives `rules` a last match at `p`.
    proof fn lemma_last_match_some(rules: Seq<Rule<S>>, i: int, arch: Arch, ev: Event, p: nat)
        requires 0 <= i < rules.len(), rules[i].action.precedence() == p, rules[i].eval(arch, ev)
        ensures Self::last_match(rules, arch, ev, p) is Some
        decreases rules.len()
    {
        if i < rules.len() - 1 && !(rules.last().action.precedence() == p && rules.last().eval(arch, ev)) {
            assert(rules.drop_last()[i] == rules[i]);
            Self::lemma_last_match_some(rules.drop_last(), i, arch, ev, p);
        }
    }

    /// The last match of `rules` at `p` has precedence `p`.
    proof fn lemma_last_match_precedence(rules: Seq<Rule<S>>, arch: Arch, ev: Event, p: nat)
        ensures Self::last_match(rules, arch, ev, p) matches Some(act) ==> act.precedence() == p
        decreases rules.len()
    {
        if rules.len() > 0 {
            Self::lemma_last_match_precedence(rules.drop_last(), arch, ev, p);
        }
    }

    /// Replacing rule `j` by one that matches at `p` alike, with the same action when it does,
    /// keeps the last match of `rules` at `p`.
    proof fn lemma_last_match_update(rules: Seq<Rule<S>>, j: int, rule: Rule<S>, arch: Arch, ev: Event, p: nat)
        requires
            0 <= j < rules.len(),
            (rule.action.precedence() == p && rule.eval(arch, ev))
                == (rules[j].action.precedence() == p && rules[j].eval(arch, ev)),
            rule.action.precedence() == p && rule.eval(arch, ev) ==> rule.action == rules[j].action,
        ensures Self::last_match(rules.update(j, rule), arch, ev, p) == Self::last_match(rules, arch, ev, p)
        decreases rules.len()
    {
        let updated = rules.update(j, rule);
        if j == rules.len() - 1 {
            assert(updated.drop_last() =~= rules.drop_last());
        } else {
            assert(rules.drop_last()[j] == rules[j]);
            assert(updated.drop_last() =~= rules.drop_last().update(j, rule));
            Self::lemma_last_match_update(rules.drop_last(), j, rule, arch, ev, p);
        }
    }

    /// Appending rules that agree on `archs` keeps two sequences taking the same last matches.
    pub(super) proof fn lemma_same_matches_push(rules: Seq<Rule<S>>, other: Seq<Rule<S>>, archs: Seq<Arch>,
        rule: Rule<S>, other_rule: Rule<S>)
        requires
            Self::same_matches(rules, other, archs),
            rule.action == other_rule.action,
            forall |a: Arch, ev: Event| archs.contains(a) ==> #[trigger] rule.eval(a, ev) == other_rule.eval(a, ev),
        ensures Self::same_matches(rules.push(rule), other.push(other_rule), archs)
    {
        assert forall |arch: Arch, ev: Event, p: nat| archs.contains(arch) implies
            #[trigger] Self::last_match(rules.push(rule), arch, ev, p)
                == Self::last_match(other.push(other_rule), arch, ev, p) by {
            assert(rules.push(rule).drop_last() =~= rules);
            assert(other.push(other_rule).drop_last() =~= other);
            assert(Self::last_match(rules, arch, ev, p) == Self::last_match(other, arch, ev, p));
            assert(rule.eval(arch, ev) == other_rule.eval(arch, ev));
        }
    }

    /// Appending a rule that never matches on `archs` keeps two sequences taking the same last matches.
    pub(super) proof fn lemma_same_matches_skip(rules: Seq<Rule<S>>, other: Seq<Rule<S>>, archs: Seq<Arch>,
        other_rule: Rule<S>)
        requires
            Self::same_matches(rules, other, archs),
            forall |a: Arch, ev: Event| archs.contains(a) ==> !#[trigger] other_rule.eval(a, ev),
        ensures Self::same_matches(rules, other.push(other_rule), archs)
    {
        assert forall |arch: Arch, ev: Event, p: nat| archs.contains(arch) implies
            #[trigger] Self::last_match(rules, arch, ev, p)
                == Self::last_match(other.push(other_rule), arch, ev, p) by {
            assert(other.push(other_rule).drop_last() =~= other);
            assert(!other_rule.eval(arch, ev));
        }
    }

    /// Merging an appended rule into an earlier rule of the same lone action keeps two sequences
    /// taking the same last matches.
    pub(super) proof fn lemma_same_matches_merge(rules: Seq<Rule<S>>, other: Seq<Rule<S>>, archs: Seq<Arch>,
        j: int, merged: Rule<S>, other_rule: Rule<S>)
        requires
            Self::same_matches(rules, other, archs),
            0 <= j < rules.len(),
            rules[j].action == other_rule.action,
            merged.action == other_rule.action,
            other_rule.action.lone(),
            forall |a: Arch, ev: Event| archs.contains(a) ==>
                #[trigger] merged.eval(a, ev) == (rules[j].eval(a, ev) || other_rule.eval(a, ev)),
        ensures Self::same_matches(rules.update(j, merged), other.push(other_rule), archs)
    {
        let updated = rules.update(j, merged);
        let act = other_rule.action;
        assert forall |arch: Arch, ev: Event, p: nat| archs.contains(arch) implies
            #[trigger] Self::last_match(updated, arch, ev, p)
                == Self::last_match(other.push(other_rule), arch, ev, p) by {
            assert(other.push(other_rule).drop_last() =~= other);
            assert(Self::last_match(rules, arch, ev, p) == Self::last_match(other, arch, ev, p));
            assert(merged.eval(arch, ev) == (rules[j].eval(arch, ev) || other_rule.eval(arch, ev)));
            if act.precedence() == p && other_rule.eval(arch, ev) {
                assert(updated[j] == merged);
                Self::lemma_last_match_some(updated, j, arch, ev, p);
                Self::lemma_last_match_precedence(updated, arch, ev, p);
                let found = Self::last_match(updated, arch, ev, p)->Some_0;
                assert(found.precedence() == act.precedence());
            } else {
                Self::lemma_last_match_update(rules, j, merged, arch, ev, p);
            }
        }
    }
}

impl<S: Syscall> Policy<S> {
    /// Dispatch at `priority` over the first `i` rules takes their last match at `priority`, if any.
    proof fn lemma_dispatch_last(self, arch: Arch, ev: Event, priority: int, i: int)
        requires 0 <= priority, 0 <= i <= self.rules@.len()
        ensures self.dispatch(arch, ev, priority, i) == match Rule::last_match(self.rules@.take(i), arch, ev, priority as nat) {
            Some(act) => act,
            None => self.dispatch(arch, ev, priority - 1, self.rules@.len() as int),
        }
        decreases i
    {
        if i > 0 {
            assert(self.rules@.take(i).drop_last() =~= self.rules@.take(i - 1));
            self.lemma_dispatch_last(arch, ev, priority, i - 1);
        }
    }

    /// Policies whose rules take the same last matches dispatch alike on each of their architectures.
    proof fn lemma_same_dispatch(self, other: Policy<S>, arch: Arch, ev: Event, priority: int)
        requires
            -1 <= priority,
            self.archs@.contains(arch),
            self.act_no_match == other.act_no_match,
            Rule::same_matches(self.rules@, other.rules@, self.archs@),
        ensures
            self.dispatch(arch, ev, priority, self.rules@.len() as int)
                == other.dispatch(arch, ev, priority, other.rules@.len() as int),
        decreases priority + 1
    {
        if priority >= 0 {
            self.lemma_dispatch_last(arch, ev, priority, self.rules@.len() as int);
            other.lemma_dispatch_last(arch, ev, priority, other.rules@.len() as int);
            assert(self.rules@.take(self.rules@.len() as int) =~= self.rules@);
            assert(other.rules@.take(other.rules@.len() as int) =~= other.rules@);
            assert(Rule::last_match(self.rules@, arch, ev, priority as nat)
                == Rule::last_match(other.rules@, arch, ev, priority as nat));
            self.lemma_same_dispatch(other, arch, ev, priority - 1);
        }
    }

    /// Policies whose rules take the same last matches settle on one action in their blocks from `i` on.
    proof fn lemma_same_blocks(self, other: Policy<S>, ev: Event, i: int)
        requires
            0 <= i,
            self.archs@ == other.archs@,
            self.act_no_match == other.act_no_match,
            self.act_bad_arch == other.act_bad_arch,
            Rule::same_matches(self.rules@, other.rules@, self.archs@),
        ensures self.blocks(ev, i) == other.blocks(ev, i)
        decreases self.archs@.len() - i
    {
        if i < self.archs@.len() {
            if self.archs@[i].matches_event(ev) {
                assert(self.archs@.contains(self.archs@[i]));
                self.lemma_same_dispatch(other, self.archs@[i], ev, 7);
            } else {
                self.lemma_same_blocks(other, ev, i + 1);
            }
        }
    }

    /// Policies whose rules take the same last matches, and that agree otherwise, accept the same actions.
    pub(super) proof fn lemma_same_eval(self, other: Policy<S>)
        requires
            self.wf(),
            other.wf(),
            self.archs@ == other.archs@,
            self.act_no_match == other.act_no_match,
            self.act_bad_arch == other.act_bad_arch,
            Rule::same_matches(self.rules@, other.rules@, self.archs@),
        ensures forall |ev: Event, act: Action| self.eval(ev, act) <==> other.eval(ev, act)
    {
        hide(Policy::eval);
        self.theorem_eval_functional();
        other.theorem_eval_functional();
        assert forall |ev: Event, act: Action| self.eval(ev, act) <==> other.eval(ev, act) by {
            self.lemma_blocks(ev, 0);
            other.lemma_blocks(ev, 0);
            self.lemma_same_blocks(other, ev, 0);
        }
    }
}

} // verus!
