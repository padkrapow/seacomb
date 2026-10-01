//! Rewriting one rule, and merging rules on one syscall.

use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::{policy::*, expr::*};

verus! {

impl Action {
    /// Whether no other action has this action's precedence.
    pub(super) open spec fn lone(self) -> bool {
        forall |other: Action| #[trigger] other.precedence() == self.precedence() ==> other == self
    }

    /// Returns whether no other action has this action's precedence.
    fn is_lone(&self) -> (res: bool)
        ensures res ==> self.lone()
    {
        matches!(self, Action::KillProcess | Action::KillThread | Action::Notify | Action::Log | Action::Allow)
    }
}

impl<S: Syscall> Rule<S> {
    /// Whether `other` differs from this rule only in its condition, wherever a policy over
    /// `archs` evaluates them, and has an action no other action shares a precedence with.
    pub(super) open spec fn mergeable(self, other: Rule<S>, archs: Seq<Arch>) -> bool {
        let active = self.active_archs(archs);
        &&& self.action == other.action
        &&& self.action.lone()
        &&& self.archs@ == other.archs@
        &&& self.no_mux == other.no_mux
        &&& forall |i: int| #![trigger active[i]] 0 <= i < active.len() ==> {
            &&& self.syscall.spec_nr(active[i]) == other.syscall.spec_nr(active[i])
            &&& self.syscall.spec_signature(active[i]) == other.syscall.spec_signature(active[i])
            &&& self.no_mux || self.syscall.spec_mux(active[i]) is None && other.syscall.spec_mux(active[i]) is None
        }
    }

    /// Returns this rule with its condition folded and its architectures cleared if they
    /// cover `archs`, or `None` if it is active on none of them.
    pub(super) fn rewrite(&self, archs: &[Arch]) -> (res: Option<Rule<S>>)
        requires self.wf(archs@)
        ensures
            res is None ==> forall |a: Arch, ev: Event| archs@.contains(a) ==> !#[trigger] self.eval(a, ev),
            res matches Some(r) ==> {
                &&& r.wf(archs@)
                &&& r.action == self.action
                &&& forall |a: Arch, ev: Event| archs@.contains(a) ==> #[trigger] r.eval(a, ev) == self.eval(a, ev)
            },
    {
        let mut any = false;
        let mut all = true;
        let mut i: usize = 0;
        while i < archs.len()
            invariant
                i <= archs@.len(),
                any <==> exists |k: int| 0 <= k < i && self.active_on(#[trigger] archs@[k]),
                all <==> forall |k: int| 0 <= k < i ==> self.active_on(#[trigger] archs@[k]),
            decreases archs@.len() - i
        {
            let active = self.is_active_on(archs[i]);
            any = any || active;
            all = all && active;
            i += 1;
        }
        if !any {
            return None;
        }
        Some(Rule {
            action: self.action,
            syscall: self.syscall,
            cond: Arc::new(self.cond.fold()),
            archs: if all { Vec::new() } else { vstd::slice::slice_to_vec(self.archs.as_slice()) },
            no_mux: self.no_mux,
        })
    }

    /// Returns whether this rule's syscall and `other`'s have one number and signature on
    /// `arch`, and neither is multiplexed there unless this rule forbids it.
    fn same_syscall_on(&self, other: &Rule<S>, arch: Arch) -> (res: bool)
        ensures res ==> {
            &&& self.syscall.spec_nr(arch) == other.syscall.spec_nr(arch)
            &&& self.syscall.spec_signature(arch) == other.syscall.spec_signature(arch)
            &&& self.no_mux || self.syscall.spec_mux(arch) is None && other.syscall.spec_mux(arch) is None
        }
    {
        let same_nr = match (self.syscall.nr(arch), other.syscall.nr(arch)) {
            (Some(a), Some(b)) => a == b,
            (None, None) => true,
            _ => false,
        };
        if !same_nr || !self.no_mux && (self.syscall.mux(arch).is_some() || other.syscall.mux(arch).is_some()) {
            return false;
        }
        let sig = self.syscall.signature(arch);
        let other_sig = other.syscall.signature(arch);
        if sig.len() != other_sig.len() {
            return false;
        }
        let mut i: usize = 0;
        while i < sig.len()
            invariant
                sig@.len() == other_sig@.len(),
                i <= sig@.len(),
                forall |k: int| 0 <= k < i ==> sig@[k] == other_sig@[k],
            decreases sig@.len() - i
        {
            if sig[i] != other_sig[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Returns whether `other` is mergeable into this rule over `archs`.
    fn merges_with(&self, other: &Rule<S>, archs: &[Arch]) -> (res: bool)
        ensures res ==> self.mergeable(*other, archs@)
    {
        if self.action != other.action || !self.action.is_lone() || self.no_mux != other.no_mux
            || self.archs.len() != other.archs.len() {
            return false;
        }
        let mut i: usize = 0;
        while i < self.archs.len()
            invariant
                self.archs@.len() == other.archs@.len(),
                i <= self.archs@.len(),
                forall |k: int| 0 <= k < i ==> self.archs@[k] == other.archs@[k],
            decreases self.archs@.len() - i
        {
            if self.archs[i] != other.archs[i] {
                return false;
            }
            i += 1;
        }
        proof { assert(self.archs@ =~= other.archs@); }
        let active = if self.archs.is_empty() { archs } else { self.archs.as_slice() };
        let mut i: usize = 0;
        while i < active.len()
            invariant
                self.action == other.action,
                self.action.lone(),
                self.archs@ == other.archs@,
                self.no_mux == other.no_mux,
                active@ == self.active_archs(archs@),
                i <= active@.len(),
                forall |k: int| #![trigger active@[k]] 0 <= k < i ==> {
                    &&& self.syscall.spec_nr(active@[k]) == other.syscall.spec_nr(active@[k])
                    &&& self.syscall.spec_signature(active@[k]) == other.syscall.spec_signature(active@[k])
                    &&& self.no_mux || self.syscall.spec_mux(active@[k]) is None
                        && other.syscall.spec_mux(active@[k]) is None
                },
            decreases active@.len() - i
        {
            if !self.same_syscall_on(other, active[i]) {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Returns the index of a rule in `rules` that this rule is mergeable into over `archs`.
    pub(super) fn find_merge(&self, rules: &[Rule<S>], archs: &[Arch]) -> (res: Option<usize>)
        ensures res matches Some(j) ==> j < rules@.len() && rules@[j as int].mergeable(*self, archs@)
    {
        let mut j: usize = 0;
        while j < rules.len()
            invariant j <= rules@.len()
            decreases rules@.len() - j
        {
            if rules[j].merges_with(self, archs) {
                return Some(j);
            }
            j += 1;
        }
        None
    }

    /// Returns a rule that matches exactly when this rule or `other` does.
    pub(super) fn merge(&self, other: &Rule<S>, Ghost(archs): Ghost<Seq<Arch>>) -> (res: Rule<S>)
        requires self.mergeable(*other, archs), self.wf(archs), other.wf(archs)
        ensures
            res.wf(archs),
            res.action == self.action,
            forall |a: Arch, ev: Event| archs.contains(a) ==>
                #[trigger] res.eval(a, ev) == (self.eval(a, ev) || other.eval(a, ev)),
    {
        let cond = if matches!(*self.cond, Cond::True) || matches!(*other.cond, Cond::True) {
            Cond::True
        } else {
            Cond::Or(self.cond.clone(), other.cond.clone())
        };
        Rule {
            action: self.action,
            syscall: self.syscall,
            cond: Arc::new(cond),
            archs: vstd::slice::slice_to_vec(self.archs.as_slice()),
            no_mux: self.no_mux,
        }
    }
}

} // verus!
