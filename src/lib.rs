#![doc = include_str!("../README.md")]

#![deny(unsafe_op_in_unsafe_fn)]
#![deny(unused_must_use)]
#![deny(dangling_pointers_from_locals)]
#![deny(dangling_pointers_from_temporaries)]

#![warn(unnameable_types)]
#![warn(unreachable_pub)]
#![warn(clippy::undocumented_unsafe_blocks)]

mod asm;
mod check;
mod compiler;
mod macros;
mod spec;
pub mod prop;

use vstd::prelude::*;
use std::sync::Arc;

pub use crate::compiler::CompileError;
pub use crate::check::CheckError;
pub use crate::spec::{policy::*, syscall::*, cbpf::*, expr::*};
pub use crate::macros::{ToExpr, ToCond};

verus! {

/// An error while creating, updating, compiling, or installing a filter.
#[verifier::external_derive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// The policy fails a well-formedness check.
    #[error("failed to validate the policy")]
    Check(#[source] CheckError),
    /// The policy could not be compiled into a filter program.
    #[error("failed to compile the policy")]
    Compile(#[source] CompileError),
    /// The filter has no architectures enabled.
    #[error("filter has no architectures enabled")]
    NoArch,
    /// The native architecture is not supported.
    #[error("native architecture is not supported")]
    UnsupportedNativeArch,
    /// The filter exceeds Linux's instruction limit.
    #[error("filter exceeds the kernel's 4096-instruction limit")]
    FilterTooLarge,
    /// Failed to set `no_new_privs`.
    #[error("failed to set no_new_privs: {}", std::io::Error::from_raw_os_error(*.0))]
    NoNewPrivsFailed(i32),
    /// Failed to install the seccomp filter.
    #[error("failed to install the seccomp filter: {}", std::io::Error::from_raw_os_error(*.0))]
    InstallFailed(i32),
}

impl Arch {
    /// Returns the architecture this binary runs on, or an error if it is unsupported.
    pub fn native() -> Result<Arch, Error> {
        if cfg!(all(target_arch = "x86_64", target_pointer_width = "64")) {
            Ok(Arch::X86_64)
        } else if cfg!(target_arch = "aarch64") {
            Ok(Arch::Aarch64)
        } else if cfg!(target_arch = "x86") {
            Ok(Arch::X86)
        } else if cfg!(target_arch = "arm") {
            Ok(Arch::Arm)
        } else {
            Err(Error::UnsupportedNativeArch)
        }
    }
}

/// A policy under construction and its filter options.
#[derive(Debug, Clone, PartialEq, Eq)]
// Verus does not yet model non-Copy Clone derives.
#[verifier::external_derive(Clone)]
pub struct Filter {
    policy: Policy,
    /// Set `no_new_privs` before installing the filter.
    ctl_nnp: bool,
    /// Synchronize the installed filter across all threads.
    ctl_tsync: bool,
    /// Request logging of all filter actions except `Allow`.
    ctl_log: bool,
    // TODO: Support `ctl_waitkill`
}

impl Filter {
    pub closed spec fn wf(self) -> bool {
        self.policy.wf()
    }

    pub closed spec fn policy(self) -> Policy {
        self.policy
    }

    /// Creates a filter with default action `act_no_match` and no architectures enabled.
    pub fn new(act_no_match: Action) -> (res: Result<Filter, Error>)
        ensures res matches Ok(f) ==> {
            &&& f.wf()
            &&& f.policy().act_no_match == act_no_match
            &&& f.policy().act_bad_arch == Action::KillThread
            &&& f.policy().archs@.len() == 0
            &&& f.policy().rules@.len() == 0
        }
    {
        if let Err(err) = act_no_match.check() {
            return Err(Error::Check(err));
        }
        Ok(Filter {
            policy: Policy {
                archs: Vec::new(),
                rules: Vec::new(),
                act_no_match,
                act_bad_arch: Action::KillThread,
            },
            ctl_nnp: true,
            ctl_tsync: false,
            ctl_log: false,
        })
    }

    /// Creates a filter over the running architecture with default action `act_no_match`.
    pub fn new_native(act_no_match: Action) -> (res: Result<Filter, Error>)
        ensures res matches Ok(f) ==> {
            &&& f.wf()
            &&& f.policy().act_no_match == act_no_match
            &&& f.policy().act_bad_arch == Action::KillThread
            &&& f.policy().archs@.len() == 1
            &&& f.policy().rules@.len() == 0
        }
    {
        let mut filter = Self::new(act_no_match)?;
        filter.add_arch(Arch::native()?)?;
        Ok(filter)
    }

    /// Adds `arch` to the architectures covered by this filter's rules.
    pub fn add_arch(&mut self, arch: Arch) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy().act_no_match == old(self).policy().act_no_match,
            final(self).policy().act_bad_arch == old(self).policy().act_bad_arch,
            final(self).policy().rules == old(self).policy().rules,
            res is Ok ==> final(self).policy().archs@ == old(self).policy().archs@.push(arch),
            res is Err ==> final(self).policy() == old(self).policy(),
    {
        let mut i: usize = 0;
        while i < self.policy.archs.len()
            invariant
                self.wf(),
                i <= self.policy.archs@.len(),
                forall |k: int| #![trigger self.policy.archs@[k]]
                    0 <= k < i ==> self.policy.archs@[k] != arch,
            decreases self.policy.archs@.len() - i
        {
            if self.policy.archs[i] == arch {
                return Err(Error::Check(CheckError::DuplicateArch));
            }
            i += 1;
        }

        let mut prospective = self.policy.archs.clone();
        prospective.push(arch);
        let mut r: usize = 0;
        while r < self.policy.rules.len()
            invariant
                self.wf(),
                prospective@ == self.policy.archs@.push(arch),
                r <= self.policy.rules@.len(),
                forall |k: int| 0 <= k < r ==>
                    #[trigger] self.policy.rules@[k].wf(prospective@),
            decreases self.policy.rules@.len() - r
        {
            if let Err(err) = self.policy.rules[r].check(prospective.as_slice()) {
                return Err(Error::Check(err));
            }
            r += 1;
        }

        let ghost prev = self.policy.archs@;
        self.policy.archs.push(arch);
        proof {
            assert forall |k: int, l: int| 0 <= k < l < self.policy.archs@.len()
                implies #[trigger] self.policy.archs@[k] != #[trigger] self.policy.archs@[l] by {
                if l < prev.len() {
                    assert(prev[k] != prev[l]);
                } else {
                    assert(prev[k] != arch);
                }
            }
            assert forall |k: int| 0 <= k < self.policy.rules@.len()
                implies #[trigger] self.policy.rules@[k].wf(self.policy.archs@) by {
                assert(self.policy.rules@[k].wf(prospective@));
            }
        }
        Ok(())
    }

    /// Applies `action` to `syscall` when `cond` holds.
    pub fn add_rule(&mut self, action: Action, syscall: Syscall, cond: Cond) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy().archs == old(self).policy().archs,
            final(self).policy().act_no_match == old(self).policy().act_no_match,
            final(self).policy().act_bad_arch == old(self).policy().act_bad_arch,
            res is Ok ==> {
                let rule = final(self).policy().rules@.last();
                &&& final(self).policy().rules@ == old(self).policy().rules@.push(rule)
                &&& rule.action == action
                &&& rule.syscall == syscall
                &&& *rule.cond == cond
                &&& rule.archs@ == seq![]
                &&& rule.no_mux == false
            },
            res is Err ==> final(self).policy() == old(self).policy(),
    {
        self.add_rule_internal(Rule { action, syscall, cond: Arc::new(cond), archs: Vec::new(), no_mux: false })
    }

    /// Applies `action` to `syscall` when `cond` holds, on the architectures in `archs` only.
    pub fn add_rule_on_archs(&mut self, action: Action, syscall: Syscall, cond: Cond, archs: &[Arch])
        -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy().archs == old(self).policy().archs,
            final(self).policy().act_no_match == old(self).policy().act_no_match,
            final(self).policy().act_bad_arch == old(self).policy().act_bad_arch,
            res is Ok ==> {
                let rule = final(self).policy().rules@.last();
                &&& final(self).policy().rules@ == old(self).policy().rules@.push(rule)
                &&& rule.action == action
                &&& rule.syscall == syscall
                &&& *rule.cond == cond
                &&& rule.archs@ == archs@
                &&& rule.no_mux == false
            },
            res is Err ==> final(self).policy() == old(self).policy(),
    {
        let archs = vstd::slice::slice_to_vec(archs);
        self.add_rule_internal(Rule { action, syscall, cond: Arc::new(cond), archs, no_mux: false })
    }

    /// Adds a rule for the exact syscall number only. For example, on x86,
    /// while `bind(..)` and `socketcall(2, ..)` have the same behavior,
    /// adding a rule for `Syscall::Bind` only applies to the first case.
    pub fn add_rule_exact(&mut self, action: Action, syscall: Syscall, cond: Cond) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy().archs == old(self).policy().archs,
            final(self).policy().act_no_match == old(self).policy().act_no_match,
            final(self).policy().act_bad_arch == old(self).policy().act_bad_arch,
            res is Ok ==> {
                let rule = final(self).policy().rules@.last();
                &&& final(self).policy().rules@ == old(self).policy().rules@.push(rule)
                &&& rule.action == action
                &&& rule.syscall == syscall
                &&& *rule.cond == cond
                &&& rule.archs@ == seq![]
                &&& rule.no_mux == true
            },
            res is Err ==> final(self).policy() == old(self).policy(),
    {
        self.add_rule_internal(Rule { action, syscall, cond: Arc::new(cond), archs: Vec::new(), no_mux: true })
    }

    /// Adds a rule for the exact syscall number only, on the architectures in `archs` only.
    pub fn add_rule_exact_on_archs(&mut self, action: Action, syscall: Syscall, cond: Cond, archs: &[Arch])
        -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy().archs == old(self).policy().archs,
            final(self).policy().act_no_match == old(self).policy().act_no_match,
            final(self).policy().act_bad_arch == old(self).policy().act_bad_arch,
            res is Ok ==> {
                let rule = final(self).policy().rules@.last();
                &&& final(self).policy().rules@ == old(self).policy().rules@.push(rule)
                &&& rule.action == action
                &&& rule.syscall == syscall
                &&& *rule.cond == cond
                &&& rule.archs@ == archs@
                &&& rule.no_mux == true
            },
            res is Err ==> final(self).policy() == old(self).policy(),
    {
        let archs = vstd::slice::slice_to_vec(archs);
        self.add_rule_internal(Rule { action, syscall, cond: Arc::new(cond), archs, no_mux: true })
    }

    fn add_rule_internal(&mut self, rule: Rule) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy().archs == old(self).policy().archs,
            final(self).policy().act_no_match == old(self).policy().act_no_match,
            final(self).policy().act_bad_arch == old(self).policy().act_bad_arch,
            res is Ok ==> final(self).policy().rules@ == old(self).policy().rules@.push(rule),
            res is Err ==> final(self).policy() == old(self).policy(),
    {
        if let Err(err) = rule.check(self.policy.archs.as_slice()) {
            return Err(Error::Check(err));
        }
        // NOTE: libseccomp enforces that the action cannot be the default action,
        // but we do not have that restriction.

        let ghost prev = self.policy.rules@;
        self.policy.rules.push(rule);
        proof {
            assert forall |k: int| 0 <= k < self.policy.rules@.len()
                implies #[trigger] self.policy.rules@[k].wf(self.policy.archs@) by {
                if k < prev.len() {
                    assert(prev[k].wf(self.policy.archs@));
                }
            }
        }
        Ok(())
    }

    /// Sets the action for syscalls from architectures this filter does not cover.
    pub fn on_bad_arch(&mut self, act: Action) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy().archs == old(self).policy().archs,
            final(self).policy().rules == old(self).policy().rules,
            final(self).policy().act_no_match == old(self).policy().act_no_match,
            res is Ok ==> final(self).policy().act_bad_arch == act,
            res is Err ==> final(self).policy() == old(self).policy(),
    {
        if let Err(err) = act.check() {
            return Err(Error::Check(err));
        }
        self.policy.act_bad_arch = act;
        Ok(())
    }

    /// Skips setting `no_new_privs` during filter installation.
    pub fn allow_new_privileges(&mut self)
        ensures
            final(self).wf() == old(self).wf(),
            final(self).policy() == old(self).policy(),
    {
        self.ctl_nnp = false;
    }

    /// When installing, set all threads in this process to use the same seccomp filter chain.
    pub fn enable_thread_sync(&mut self)
        ensures
            final(self).wf() == old(self).wf(),
            final(self).policy() == old(self).policy(),
    {
        self.ctl_tsync = true;
    }

    /// Requests kernel audit records for non-allow actions when installing the filter
    /// (requires `auditd` and [ausearch(8)](https://man7.org/linux/man-pages/man8/ausearch.8.html) to view logs).
    pub fn request_audit_logging(&mut self)
        ensures
            final(self).wf() == old(self).wf(),
            final(self).policy() == old(self).policy(),
    {
        self.ctl_log = true;
    }
}

#[cfg(target_os = "linux")]
impl Error {
    /// The errno the last failing libc call left behind.
    #[verifier::external_body]
    fn errno() -> i32 {
        std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
    }
}

#[cfg(target_os = "linux")]
impl Filter {
    /// The `SECCOMP_FILTER_FLAG_*` bits in `linux/seccomp.h`.
    const FLAG_TSYNC: u64 = 1 << 0;
    const FLAG_LOG: u64 = 1 << 1;

    /// Generates a flag for `seccomp(2)`
    fn filter_flags(&self) -> u64 {
        let mut flags: u64 = 0;
        if self.ctl_tsync {
            flags |= Self::FLAG_TSYNC;
        }
        if self.ctl_log {
            flags |= Self::FLAG_LOG;
        }
        flags
    }

    /// Compiles this filter and installs it on the calling thread.
    #[verifier::external_body]
    pub fn install(&self) -> Result<(), Error>
        requires self.wf()
    {
        if self.policy.archs.is_empty() {
            return Err(Error::NoArch);
        }
        let program = match self.policy.to_cbpf() {
            Ok(program) => program,
            Err(err) => return Err(Error::Compile(err)),
        };

        // `BPF_MAXINSNS` in `linux/bpf_common.h`.
        if program.instrs.len() > 4096 {
            return Err(Error::FilterTooLarge);
        }

        // `seccomp()` answers EACCES to a thread that holds neither CAP_SYS_ADMIN nor
        // `no_new_privs`, so `ctl_nnp` goes in first.
        if self.ctl_nnp {
            // SAFETY: PR_SET_NO_NEW_PRIVS takes only scalar arguments and accesses no user buffer.
            let rc = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
            if rc != 0 {
                return Err(Error::NoNewPrivsFailed(Error::errno()));
            }
        }

        let raw = program.assemble();
        let rc = raw.install_with_flags(self.filter_flags());
        if rc != 0 {
            // A thread that refuses TSYNC comes back as its own id rather than as -1,
            // unless `SECCOMP_FILTER_FLAG_TSYNC_ESRCH` is set, which this module leaves off.
            let errno = if rc < 0 { Error::errno() } else { libc::ESRCH };
            return Err(Error::InstallFailed(errno));
        }
        Ok(())
    }
}

} // verus!
