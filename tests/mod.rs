//! Tests of the public API against the host kernel.

#![cfg(target_os = "linux")]
#![deny(unsafe_op_in_unsafe_fn)]

mod cond;
mod filter;

use seacomb::*;
use seacomb::PrimType::*;

/// The result a syscall should come back with.
#[derive(Debug, Clone, Copy)]
enum Expect {
    Ok,
    /// Result of a custom "deny" action.
    Denied,
    Errno(i32),
    Sigsys,
}

impl Expect {
    /// The errno the filters under test deny with, which no syscall returns on its own.
    const DENIED: u16 = 4000;

    /// The `SCMP_ACT_ERRNO` action that answers with `Self::DENIED`.
    const DENY: Action = Action::Errno(Self::DENIED);

    /// The errno the last failing libc call left behind.
    fn errno() -> i32 {
        std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
    }

    /// Whether a call that returned `ret` and left `errno` behind, or whose child `outcome` was killed by a signal, came back as expected.
    fn matches(self, outcome: Result<(libc::c_long, i32), libc::c_int>) -> bool {
        match (self, outcome) {
            (Expect::Ok, Ok((ret, _))) => ret != -1,
            (Expect::Denied, Ok((ret, errno))) => ret == -1 && errno == Self::DENIED as i32,
            (Expect::Errno(e), Ok((ret, errno))) => ret == -1 && errno == e,
            (Expect::Sigsys, Err(signal)) => signal == libc::SIGSYS,
            _ => false,
        }
    }
}

/// Test helpers on `Filter`.
trait FilterExt {
    /// Returns a native filter with default action `default` and the one rule `rule`.
    fn new_native_with_rule(default: Action, rule: Rule) -> Result<Filter, Error>;

    /// Returns a native filter that allows by default and has the one rule `rule`.
    fn new_native_allow(rule: Rule) -> Filter;

    /// Returns a filter over `archs` that allows by default, or the error adding `archs` or `rule` gave.
    fn with_rule(archs: &[Arch], rule: Rule) -> Result<Filter, Error>;

    /// Runs `call`, which must leave Rust's memory alone, in a child that has this filter installed, and returns its result or the signal that killed the child.
    unsafe fn install_and_run<A: Copy>(&self, call: impl FnOnce() -> A) -> Result<A, libc::c_int>;

    /// Makes syscall `nr` with `args`, which must leave Rust's memory alone, in a child that has this filter installed, and asserts it comes back as `expect`.
    unsafe fn install_and_check(&self, nr: libc::c_long, args: [libc::c_ulong; 6], expect: Expect);
}

impl FilterExt for Filter {
    fn new_native_with_rule(default: Action, rule: Rule) -> Result<Filter, Error> {
        let mut filter = Filter::new_native(default)?;
        filter.add(rule)?;
        Ok(filter)
    }

    #[track_caller]
    fn new_native_allow(rule: Rule) -> Filter {
        Filter::new_native_with_rule(Action::Allow, rule).unwrap()
    }

    fn with_rule(archs: &[Arch], rule: Rule) -> Result<Filter, Error> {
        let mut filter = Filter::new(Action::Allow)?;
        for &arch in archs {
            filter.add_arch(arch)?;
        }
        filter.add(rule)?;
        Ok(filter)
    }

    unsafe fn install_and_run<A: Copy>(&self, call: impl FnOnce() -> A) -> Result<A, libc::c_int> {
        // The child hands back its result through shared memory, since the filter may deny any syscall to do it with.
        let size = std::mem::size_of::<A>().max(1);
        let prot = libc::PROT_READ | libc::PROT_WRITE;
        let shared = unsafe { libc::mmap(std::ptr::null_mut(), size, prot, libc::MAP_SHARED | libc::MAP_ANONYMOUS, -1, 0) };
        assert_ne!(shared, libc::MAP_FAILED, "mmap failed");
        let shared = shared.cast::<A>();
        let pid = unsafe { libc::fork() };
        assert!(pid >= 0, "fork failed");
        if pid == 0 {
            // A denied exit would leave the child spinning, so cap how long it lives.
            unsafe { libc::alarm(10) };
            if self.install().is_err() {
                unsafe { libc::_exit(1) };
            }
            unsafe { shared.write(call()) };
            unsafe { libc::_exit(0) };
        }
        let mut status = 0;
        assert_eq!(unsafe { libc::waitpid(pid, &mut status, 0) }, pid, "waitpid failed");
        let outcome = if libc::WIFSIGNALED(status) {
            Err(libc::WTERMSIG(status))
        } else {
            assert!(libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0, "failed to install {self:?}");
            Ok(unsafe { shared.read() })
        };
        unsafe { libc::munmap(shared.cast(), size) };
        outcome
    }

    #[track_caller]
    unsafe fn install_and_check(&self, nr: libc::c_long, args: [libc::c_ulong; 6], expect: Expect) {
        let [a, b, c, d, e, f] = args;
        let call = || (unsafe { libc::syscall(nr, a, b, c, d, e, f) }, Expect::errno());
        let outcome = unsafe { self.install_and_run(call) };
        assert!(expect.matches(outcome), "syscall {nr} with {args:?} should come back as {expect:?} under {self:?}");
    }
}
