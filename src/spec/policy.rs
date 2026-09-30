//! Abstract syntax and semantics of the libseccomp policy language.

use vstd::prelude::*;
use std::sync::Arc;
use super::expr::*;

// Syntax
verus! {

/// All supported architectures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum Arch { X86, X86_64, Arm, Aarch64 }

/// Actions that a policy can take on a syscall event.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum Action {
    /// Kill the current process.
    KillProcess,
    /// Kill the current thread.
    KillThread,
    /// Send `SIGSYS` to the current thread, with the value in `si_errno`.
    Trap(u16),
    /// Fail the syscall with the value as its errno.
    Errno(u16),
    /// Notify the ptrace tracer, with the value as its event message.
    Trace(u16),
    /// Allow the syscall and add it to the kernel audit log.
    Log,
    /// Allow the syscall.
    Allow,
    /// Forward the syscall to the user-space notification listener.
    Notify,
}

/// Abstraction for syscall symbols with type signatures.
pub trait Syscall: Copy {
    spec fn spec_nr(self, arch: Arch) -> Option<i32>;
    spec fn spec_signature(self, arch: Arch) -> Seq<PrimType>;
    spec fn spec_mux(self, arch: Arch) -> Option<(Self, Cond)>;

    /// Returns the syscall number for this symbol.
    fn nr(self, arch: Arch) -> (res: Option<i32>)
        ensures res == self.spec_nr(arch);

    /// Returns the type signature for this symbol.
    fn signature(self, arch: Arch) -> (res: &'static [PrimType])
        ensures res@ =~= self.spec_signature(arch);

    /// Looks up the symbol by name (only used by macros).
    fn lookup(name: &str) -> Option<Self>;

    /// Returns whether the given symbol have a multiplexed syscall
    /// (e.g., `socket(..)` is multiplexed with `socketcall(1, ..)`)
    fn mux(self, arch: Arch) -> (res: Option<(Self, Cond)>)
        ensures res == self.spec_mux(arch);
}

/// A policy rule, which applies an action to a syscall event if
/// certain condition is satisfied.
#[derive(Debug, Clone, PartialEq, Eq)]
// Verus does not yet model non-Copy Clone derives.
#[verifier::external_derive(Clone)]
pub struct Rule<S: Syscall> {
    pub action: Action,
    pub syscall: S,
    pub cond: Arc<Cond>,
    /// Limits the rule to the given list of archs.
    /// If empty, uses the global supported archs.
    pub archs: Vec<Arch>,
    /// Prevents multiplexing syscalls. For example, a rule for `bind`
    /// should not match `socketcall(2, ...)`.
    pub no_mux: bool,
}

/// A set of rules with default actions for no-match and bad-arch cases.
#[derive(Debug, Clone, PartialEq, Eq)]
// Verus does not yet model non-Copy Clone derives.
#[verifier::external_derive(Clone)]
pub struct Policy<S: Syscall> {
    pub archs: Vec<Arch>,
    pub rules: Vec<Rule<S>>,
    /// Default action when the arch is supported but no rule matches.
    pub act_no_match: Action,
    /// Default action when the arch is not supported.
    pub act_bad_arch: Action,
}

impl Action {
    /// Largest errno Linux returns for `SECCOMP_RET_ERRNO` (`include/linux/err.h`).
    pub const MAX_ERRNO: u32 = 4095;

    /// Whether the action's payload can be returned without kernel clamping.
    pub open spec fn wf(self) -> bool {
        match self {
            Action::Errno(e) => (e as u32) <= Self::MAX_ERRNO,
            _ => true,
        }
    }

    /// Higher-precedence actions override lower ones.
    /// This behavior is similar to when we install multiple filters:
    /// <https://docs.kernel.org/userspace-api/seccomp_filter.html#return-values>.
    ///
    /// NOTE that, e.g., `Errno(1)` and `Errno(2)` are not ordered.
    pub open spec fn precedence(self) -> nat {
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
}

impl<S: Syscall> Rule<S> {
    /// Active architectures, given the global default architectures.
    ///
    /// NOTE: Even under the `wf()` condition, a rule may still contain
    /// architectures that are not in `default_archs`, which is an intentional
    /// choice to allow more flexibility at the API level.
    pub open spec fn active_archs(self, default_archs: Seq<Arch>) -> Seq<Arch> {
        if self.archs@.len() == 0 {
            default_archs
        } else {
            self.archs@
        }
    }

    /// Well-formedness of a rule, relative to all supported architectures.
    pub open spec fn wf(self, default_archs: Seq<Arch>) -> bool {
        let active_archs = self.active_archs(default_archs);
        &&& self.action.wf()
        // Local active arch list is well-formed
        // NOTE: we don't require them to be a subset of `default_archs`
        &&& forall |i: int, j: int| #![trigger self.archs@[i], self.archs@[j]]
                0 <= i < j < self.archs@.len() ==> self.archs@[i] != self.archs@[j]
        // The condition is well-formed under every active arch
        &&& forall |i: int| 0 <= i < active_archs.len() ==>
                self.cond.wf(#[trigger] active_archs[i], self.syscall.spec_signature(active_archs[i]))
        // When allowing mux, the rule should not have any conditions
        // since the multiplexed call may have different argument positions.
        &&& !self.no_mux ==> forall |i: int| 0 <= i < active_archs.len() ==>
                (self.syscall.spec_mux(#[trigger] active_archs[i]) matches Some((mux, cond)) ==>
                *self.cond == Cond::True && cond.wf(active_archs[i], mux.spec_signature(active_archs[i])))
        // If a rule's syscall differ in signature on two different supported architectures,
        // it must not impose a condition on the argument.
        &&& forall |i: int, j: int| #![trigger active_archs[i], active_archs[j]]
                0 <= i < j < active_archs.len() &&
                self.syscall.spec_signature(active_archs[i]) != self.syscall.spec_signature(active_archs[j])
                ==> *self.cond == Cond::True
    }
}

impl<S: Syscall> Policy<S> {
    pub open spec fn wf(self) -> bool {
        &&& self.act_no_match.wf()
        &&& self.act_bad_arch.wf()
        // No duplicate architectures
        &&& forall |i: int, j: int| #![trigger self.archs@[i], self.archs@[j]]
                0 <= i < j < self.archs@.len() ==> self.archs@[i] != self.archs@[j]
        // Each rule is well-formed.
        &&& forall |i: int| #![trigger self.rules@[i]]
                0 <= i < self.rules@.len() ==> self.rules@[i].wf(self.archs@)
    }
}

} // verus!

// Semantics
verus! {

/// A model of a syscall event generated by the kernel
/// (i.e., [`seccomp_data`](https://man7.org/linux/man-pages/man2/seccomp.2.html)).
pub struct Event {
    pub arch: u32,
    pub nr: i32,
    pub args: Seq<u64>,
}

impl Arch {
    // `AUDIT_ARCH_*` in `linux/audit.h`.
    pub const TOKEN_X86: u32 = 0x4000_0003;
    pub const TOKEN_X86_64: u32 = 0xC000_003E;
    pub const TOKEN_ARM: u32 = 0x4000_0028;
    pub const TOKEN_AARCH64: u32 = 0xC000_00B7;

    /// Returns the arch token reported by the kernel (`linux/audit.h`).
    pub open spec fn token(self) -> u32 {
        match self {
            Arch::X86 => Self::TOKEN_X86,
            Arch::X86_64 => Self::TOKEN_X86_64,
            Arch::Arm => Self::TOKEN_ARM,
            Arch::Aarch64 => Self::TOKEN_AARCH64,
        }
    }

    /// Default 64-bit ABIs: each argument takes one slot.
    pub open spec fn interp_args_64bit(self, args: Seq<u64>, sig: Seq<PrimType>) -> Seq<u64> {
        Seq::new(sig.len(), |i: int| args[i])
    }

    /// x86 ABI: 64-bit arguments take two slots while others take one.
    pub open spec fn interp_args_x86(args: Seq<u64>, sig: Seq<PrimType>) -> Seq<u64>
        decreases sig.len()
    {
        if sig.len() == 0 {
            seq![]
        } else if sig[0].bits(Arch::X86) == 64 {
            let value = (args[0] & 0xFFFF_FFFFu64)
                      | (args[1] & 0xFFFF_FFFFu64) << 32u64;
            seq![value] + Self::interp_args_x86(args.skip(2), sig.drop_first())
        } else {
            seq![args[0]] + Self::interp_args_x86(args.drop_first(), sig.drop_first())
        }
    }

    /// ARM EABI: like x86, but a 64-bit value is padded to an even slot.
    pub open spec fn interp_args_arm(args: Seq<u64>, sig: Seq<PrimType>, slot: int) -> Seq<u64>
        decreases sig.len()
    {
        if sig.len() == 0 {
            seq![]
        } else if sig[0].bits(Arch::Arm) == 64 {
            let slot = slot + slot % 2;
            let value = (args[slot] & 0xFFFF_FFFFu64)
                      | (args[slot + 1] & 0xFFFF_FFFFu64) << 32u64;
            seq![value] + Self::interp_args_arm(args, sig.drop_first(), slot + 2)
        } else {
            seq![args[slot]] + Self::interp_args_arm(args, sig.drop_first(), slot + 1)
        }
    }

    /// The bits of each argument of a syscall with signature `sig`, as the kernel reads them from the raw `args`.
    pub open spec fn interp_args(self, args: Seq<u64>, sig: Seq<PrimType>) -> Seq<u64> {
        match self {
            Arch::X86 => Self::interp_args_x86(args, sig),
            Arch::Arm => Self::interp_args_arm(args, sig, 0),
            _ => self.interp_args_64bit(args, sig),
        }
    }
}

impl Event {
    /// Parses a (little-endian) `seccomp_data` from the kernel into an `Event`.
    pub open spec fn parse(data: &[u8]) -> Option<Event> {
        if data@.len() != 64 {
            None
        } else {
            Some(Event {
                nr: ((data@[0] as u32) | (data@[1] as u32) << 8 | (data@[2] as u32) << 16 | (data@[3] as u32) << 24) as i32,
                arch: (data@[4] as u32) | (data@[5] as u32) << 8 | (data@[6] as u32) << 16 | (data@[7] as u32) << 24,
                // Offset 8 is `instruction_pointer`, which `Event` drops.
                args: Seq::new(
                    6,
                    |k: int| (data@[16 + 8 * k] as u64)
                        | (data@[17 + 8 * k] as u64) << 8
                        | (data@[18 + 8 * k] as u64) << 16
                        | (data@[19 + 8 * k] as u64) << 24
                        | (data@[20 + 8 * k] as u64) << 32
                        | (data@[21 + 8 * k] as u64) << 40
                        | (data@[22 + 8 * k] as u64) << 48
                        | (data@[23 + 8 * k] as u64) << 56,
                ),
            })
        }
    }
}

impl Action {
    pub const RET_ACTION: u32 = 0xffff_0000;
    pub const RET_DATA: u32 = 0x0000_ffff;

    pub const RET_KILL_PROCESS: u32 = 0x8000_0000;
    pub const RET_KILL_THREAD: u32 = 0x0000_0000;
    pub const RET_TRAP: u32 = 0x0003_0000;
    pub const RET_ERRNO: u32 = 0x0005_0000;
    pub const RET_USER_NOTIF: u32 = 0x7fc0_0000;
    pub const RET_TRACE: u32 = 0x7ff0_0000;
    pub const RET_LOG: u32 = 0x7ffc_0000;
    pub const RET_ALLOW: u32 = 0x7fff_0000;

    /// Converts to the raw return value used in the BPF program.
    pub open spec fn to_ret(&self) -> u32 {
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

impl<S: Syscall> Rule<S> {
    /// Whether this rule matches event `ev` on `arch`.
    pub open spec fn eval(self, arch: Arch, ev: Event) -> bool {
        let sig = self.syscall.spec_signature(arch);
        (self.archs@.len() == 0 || self.archs@.contains(arch)) && {
            ||| self.syscall.spec_nr(arch) == Some(ev.nr) &&
                self.cond.eval(arch, sig, arch.interp_args(ev.args, sig))
            // Alternatively, there could be a multiplexed syscall on certain archs,
            // e.g., `socket` and `socketcall` on x86.
            ||| {
                &&& !self.no_mux
                &&& self.syscall.spec_mux(arch) matches Some((mux, cond))
                &&& mux.spec_nr(arch) == Some(ev.nr)
                &&& cond.eval(arch, mux.spec_signature(arch), arch.interp_args(ev.args, mux.spec_signature(arch)))
            }
        }
    }
}

impl<S: Syscall> Policy<S> {
    pub open spec fn is_active_arch(self, arch: Arch, ev: Event) -> bool {
        &&& self.archs@.contains(arch)
        &&& ev.arch == arch.token()
        // Reject x32 syscall numbers, except -1, which a tracer uses to skip a syscall.
        &&& arch == Arch::X86_64 ==> ev.nr & 0x40000000 == 0 || ev.nr == -1
    }

    /// Defines whether evaluating the policy on event `ev`
    /// results in the action `act`, which may not be unique.
    pub open spec fn eval(self, ev: Event, act: Action) -> bool
        recommends self.wf(),
    {
        // The event is not from an active arch.
        ||| act == self.act_bad_arch && forall |a: Arch| !self.is_active_arch(a, ev)
        // Exists a rule that, when evaluated on an active arch, matches the event and has the action `act`.
        ||| exists |a: Arch, i: int| {
            &&& self.is_active_arch(a, ev)
            &&& 0 <= i < self.rules@.len()
            &&& #[trigger] self.rules@[i].eval(a, ev)
            &&& self.rules@[i].action == act
            // A disambiguation rule following kernel's behavior:
            // 1. Higher precedence actions win.
            // 2. If two actions have the same precedence (e.g. `Errno(1)` and `Errno(2)`),
            //    the rule that was added last wins.
            //
            // In particular, this makes installing multiple filters more well-behaved
            // see for example [`crate::prop::theorem_eval_chain_compiled`].
            &&& forall |j: int| #![trigger self.rules@[j]]
                    0 <= j < self.rules@.len() && j != i && self.rules@[j].eval(a, ev)
                    ==> {
                        ||| self.rules@[j].action.precedence() < act.precedence()
                        ||| j < i && self.rules@[j].action.precedence() == act.precedence()
                    }
        }
        // Take the default action when no rule matches on any active arch.
        ||| {
            &&& act == self.act_no_match
            &&& exists |a: Arch| #[trigger] self.is_active_arch(a, ev)
            &&& forall |a: Arch, i: int|
                    self.is_active_arch(a, ev) && 0 <= i < self.rules@.len()
                    ==> !#[trigger] self.rules@[i].eval(a, ev)
        }
    }
}

} // verus!
