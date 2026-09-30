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

pub use crate::compiler::CompileError;
pub use crate::check::CheckError;
pub use crate::spec::{policy::*, syscall::*, expr::*};
pub use crate::spec::cbpf;
pub use crate::macros::{ToExpr, ToCond};

verus! {

/// All possible errors when creating or using policies.
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
    /// The policy has no architectures enabled.
    #[error("policy has no architectures enabled")]
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

impl Policy {
    /// Creates a policy with default action `act_no_match` and no architectures enabled.
    pub fn new(act_no_match: Action) -> (res: Result<Policy, Error>)
        ensures res matches Ok(p) ==> {
            &&& p.wf()
            &&& p.act_no_match == act_no_match
            &&& p.act_bad_arch == Action::KillThread
            &&& p.archs@.len() == 0
            &&& p.rules@.len() == 0
        }
    {
        if let Err(err) = act_no_match.check() {
            return Err(Error::Check(err));
        }
        Ok(Policy {
            archs: Vec::new(),
            rules: Vec::new(),
            act_no_match,
            act_bad_arch: Action::KillThread,
        })
    }

    /// Creates a policy over the running architecture with default action `act_no_match`.
    pub fn new_native(act_no_match: Action) -> (res: Result<Policy, Error>)
        ensures res matches Ok(p) ==> {
            &&& p.wf()
            &&& p.act_no_match == act_no_match
            &&& p.act_bad_arch == Action::KillThread
            &&& p.archs@.len() == 1
            &&& p.rules@.len() == 0
        }
    {
        let mut policy = Self::new(act_no_match)?;
        policy.add_arch(Arch::native()?)?;
        Ok(policy)
    }

    /// Adds `arch` to the architectures covered by this policy's rules, unless it already exists.
    pub fn add_arch(&mut self, arch: Arch) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).act_no_match == old(self).act_no_match,
            final(self).act_bad_arch == old(self).act_bad_arch,
            final(self).rules == old(self).rules,
            old(self).archs@.contains(arch) ==> res is Ok && final(self).archs@ == old(self).archs@,
            res is Ok && !old(self).archs@.contains(arch) ==> final(self).archs@ == old(self).archs@.push(arch),
            res is Err ==> final(self).archs@ == old(self).archs@,
    {
        let mut i: usize = 0;
        while i < self.archs.len()
            invariant
                self.wf(),
                i <= self.archs@.len(),
                forall |k: int| #![trigger self.archs@[k]]
                    0 <= k < i ==> self.archs@[k] != arch,
            decreases self.archs@.len() - i
        {
            if self.archs[i] == arch {
                proof { assert(self.archs@[i as int] == arch); }
                return Ok(());
            }
            i += 1;
        }
        proof { assert(!self.archs@.contains(arch)); }

        let ghost prev = self.archs@;
        self.archs.push(arch);
        let mut r: usize = 0;
        while r < self.rules.len()
            invariant
                old(self).wf(),
                !prev.contains(arch),
                prev == old(self).archs@,
                self.archs@ == prev.push(arch),
                self.rules == old(self).rules,
                self.act_no_match == old(self).act_no_match,
                self.act_bad_arch == old(self).act_bad_arch,
                r <= self.rules@.len(),
                forall |k: int| 0 <= k < r ==>
                    #[trigger] self.rules@[k].wf(self.archs@),
            decreases self.rules@.len() - r
        {
            if let Err(err) = self.rules[r].check(self.archs.as_slice()) {
                self.archs.pop();
                proof { assert(self.archs@ =~= prev); }
                return Err(Error::Check(err));
            }
            r += 1;
        }

        proof {
            assert forall |k: int, l: int| 0 <= k < l < self.archs@.len()
                implies #[trigger] self.archs@[k] != #[trigger] self.archs@[l] by {
                if l < prev.len() {
                    assert(prev[k] != prev[l]);
                } else {
                    assert(prev[k] != arch);
                }
            }
        }
        Ok(())
    }

    /// Adds `rule` after the rules already in this policy.
    pub fn add(&mut self, rule: Rule) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).archs == old(self).archs,
            final(self).act_no_match == old(self).act_no_match,
            final(self).act_bad_arch == old(self).act_bad_arch,
            res is Ok ==> final(self).rules@ == old(self).rules@.push(rule),
            res is Err ==> *final(self) == *old(self),
    {
        if let Err(err) = rule.check(self.archs.as_slice()) {
            return Err(Error::Check(err));
        }
        // NOTE: libseccomp enforces that the action cannot be the default action,
        // but we do not have that restriction.

        let ghost prev = self.rules@;
        self.rules.push(rule);
        proof {
            assert forall |k: int| 0 <= k < self.rules@.len()
                implies #[trigger] self.rules@[k].wf(self.archs@) by {
                if k < prev.len() {
                    assert(prev[k].wf(self.archs@));
                }
            }
        }
        Ok(())
    }

    /// Sets the action for syscalls from architectures this policy does not cover.
    pub fn on_bad_arch(&mut self, act: Action) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).archs == old(self).archs,
            final(self).rules == old(self).rules,
            final(self).act_no_match == old(self).act_no_match,
            res is Ok ==> final(self).act_bad_arch == act,
            res is Err ==> *final(self) == *old(self),
    {
        if let Err(err) = act.check() {
            return Err(Error::Check(err));
        }
        self.act_bad_arch = act;
        Ok(())
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

/// Options for installing a policy, named after libseccomp's `SCMP_FLTATR_CTL_*` flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct InstallFlags {
    /// Set `no_new_privs` before installing the filter.
    pub ctl_nnp: bool,
    /// Synchronize the installed filter across all threads.
    pub ctl_tsync: bool,
    /// Request logging of all filter actions except `Allow`.
    pub ctl_log: bool,
}

impl Default for InstallFlags {
    fn default() -> InstallFlags {
        InstallFlags { ctl_nnp: true, ctl_tsync: false, ctl_log: false }
    }
}

#[cfg(target_os = "linux")]
impl InstallFlags {
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
}

#[cfg(target_os = "linux")]
impl Policy {
    /// Compiles this policy and installs it on the calling thread with the default flags.
    pub fn install(&self) -> Result<(), Error> {
        self.install_with_flags(InstallFlags::default())
    }

    /// Compiles this policy and installs it on the calling thread with `flags`.
    #[verifier::external_body]
    pub fn install_with_flags(&self, flags: InstallFlags) -> Result<(), Error> {
        if self.archs.is_empty() {
            return Err(Error::NoArch);
        }
        if let Err(err) = self.check() {
            return Err(Error::Check(err));
        }
        let program = match self.to_cbpf() {
            Ok(program) => program,
            Err(err) => return Err(Error::Compile(err)),
        };

        // `BPF_MAXINSNS` in `linux/bpf_common.h`.
        if program.instrs.len() > 4096 {
            return Err(Error::FilterTooLarge);
        }

        // `seccomp()` answers EACCES to a thread that holds neither CAP_SYS_ADMIN nor
        // `no_new_privs`, so `ctl_nnp` goes in first.
        if flags.ctl_nnp {
            // SAFETY: PR_SET_NO_NEW_PRIVS takes only scalar arguments and accesses no user buffer.
            let rc = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
            if rc != 0 {
                return Err(Error::NoNewPrivsFailed(Error::errno()));
            }
        }

        let raw = program.assemble();
        let rc = raw.install_with_flags(flags.filter_flags());
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
