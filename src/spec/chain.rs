//! Action selection for a thread's layered seccomp filters.

use vstd::prelude::*;
use super::cbpf::*;
use super::policy::*;

verus! {

impl<S: Syscall> Policy<S> {
    /// Whether a chain of well-formed policies produces `act` on `ev`.
    /// Policies are in installation order.
    pub open spec fn eval_chain(policies: Seq<Self>, ev: Event, act: Action) -> bool {
        ||| policies.len() == 0 && act == Action::Allow
        ||| exists |i: int| {
            &&& 0 <= i < policies.len()
            &&& #[trigger] policies[i].eval(ev, act)
            &&& forall |j: int, other: Action| 0 <= j < policies.len()
                && #[trigger] policies[j].eval(ev, other) ==> {
                    ||| other.precedence() < act.precedence()
                    ||| other.precedence() == act.precedence() && j <= i
                }
        }
    }
}

impl Program {
    /// Whether the filter chain produces return value `ret` on the given `seccomp_data`,
    /// where filters are in installation order.
    ///
    /// References:
    /// - <https://man7.org/linux/man-pages/man2/seccomp.2.html>
    /// - [`seccomp_run_filters`](https://github.com/torvalds/linux/blob/v7.0/kernel/seccomp.c)
    pub open spec fn eval_chain(filters: Seq<Program>, data: &[u8], ret: u32) -> bool {
        // Linux starts with RET_ALLOW and only replaces it with a higher-precedence
        // result. An all-ALLOW chain therefore discards payload bits. This also
        // models an empty chain (no installed filters) as allowing the syscall.
        ||| ret == Action::RET_ALLOW && forall |j: int| 0 <= j < filters.len() ==> {
            &&& #[trigger] filters[j].eval(data) matches Outcome::Return(other)
            &&& other & Action::RET_ACTION == Action::RET_ALLOW
        }
        ||| exists |i: int| {
            &&& 0 <= i < filters.len()
            &&& #[trigger] filters[i].eval(data) == Outcome::Return(ret)
            &&& ((ret & Action::RET_ACTION) as i32) < (Action::RET_ALLOW as i32)
            &&& forall |j: int| 0 <= j < filters.len() ==> {
                // If any filter has a cBPF runtime error, no return value satisfies the relation.
                &&& #[trigger] filters[j].eval(data) matches Outcome::Return(other)
                &&& {
                    // Compare signed action codes, ignoring payload bits; later filters win ties.
                    let priority = (ret & Action::RET_ACTION) as i32;
                    let other_priority = (other & Action::RET_ACTION) as i32;
                    priority < other_priority || (priority == other_priority && j <= i)
                }
            }
        }
    }
}

} // verus!
