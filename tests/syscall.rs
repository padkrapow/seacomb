//! Tests of policies over a custom `Syscall` table.

use super::*;

seacomb::impl_syscall! {
    /// A small set of syscall symbols for testing.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum SyscallMock {
        #[name("pid")]
        #[on(X86, 20)]
        #[on(X86_64, 39)]
        #[on(Arm, 20)]
        #[on(Aarch64, 172)]
        Pid,
        #[name("ppid")]
        #[on(X86, 64)]
        #[on(X86_64, 110)]
        #[on(Arm, 64)]
        #[on(Aarch64, 173)]
        Ppid,
        #[name("net")]
        #[on(X86, 102, I(32), Ptr)]
        Net,
        #[name("sock")]
        #[on(X86, 359, I(32), I(32), I(32))]
        #[on(X86_64, 41, I(32), I(32), I(32))]
        #[on(Arm, 281, I(32), I(32), I(32))]
        #[on(Aarch64, 198, I(32), I(32), I(32))]
        #[mux(X86, Net, @0 & 0xFFFF_FFFF == 1)]
        Sock,
    }
}

/// A table finds exactly the names it lists.
#[test]
fn lookup() {
    assert_eq!(SyscallMock::lookup("pid"), Some(SyscallMock::Pid));
    assert_eq!(SyscallMock::lookup("sock"), Some(SyscallMock::Sock));
    assert_eq!(SyscallMock::lookup("getpid"), None);
    assert_eq!(SyscallMock::lookup("pi"), None);
}

/// A `syscall` line makes a policy name syscalls from that table alone.
#[test]
fn names() {
    let policy = policy!(syscall SyscallMock; default allow on x86; errno(1) pid(); allow exact sock(domain) if domain == 2).unwrap();
    assert_eq!(policy.rules[0].syscall, SyscallMock::Pid);
    assert_eq!(policy.to_string(), "default allow on x86 else kill_thread;\nerrno(1) pid();\nallow exact sock() if @0 == 2;");
    assert!(matches!(policy!(syscall SyscallMock; default allow on x86; allow getpid()), Err(Error::UnknownSyscall("getpid"))));
    assert!(matches!(policy!(default allow on x86; allow pid()), Err(Error::UnknownSyscall("pid"))));
    assert!(policy!(syscall crate::syscall::SyscallMock; default allow on x86; allow ppid()).is_ok());
}

/// A rule over a custom table filters the syscall its number names.
#[test]
fn filter() {
    let policy = policy!(syscall SyscallMock; default allow on native; {Expect::DENY} pid()).unwrap();
    unsafe {
        policy.install_and_check(libc::SYS_getpid, [0; 6], Expect::Denied);
        policy.install_and_check(libc::SYS_getppid, [0; 6], Expect::Ok);
    }
}

/// A multiplexed custom syscall takes argument tests only in exact rules, on an arch that multiplexes it.
#[test]
fn mux_conds() {
    assert!(matches!(
        policy!(syscall SyscallMock; default allow on x86_64, x86; {Expect::DENY} sock(domain) if domain == 1),
        Err(Error::Check(CheckError::InvalidMuxConditions)),
    ));
    policy!(syscall SyscallMock; default allow on x86_64; {Expect::DENY} sock(domain) if domain == 1).unwrap();
    policy!(syscall SyscallMock; default allow on x86_64, x86; {Expect::DENY} exact sock(domain) if domain == 1).unwrap();
}

/// On x86, a custom `#[mux]` entry covers the multiplexed form, selected by its call number.
#[cfg(target_arch = "x86")]
#[test]
fn x86_mux() {
    let policy = policy!(syscall SyscallMock; default allow on native; {Expect::DENY} sock()).unwrap();
    let socket_args: [libc::c_ulong; 3] = [0; 3];
    let bind_args: [libc::c_ulong; 3] = [libc::c_ulong::MAX, 0, 0];
    unsafe {
        policy.install_and_check(libc::SYS_socket, [0; 6], Expect::Denied);
        policy.install_and_check(libc::SYS_socketcall, [1, socket_args.as_ptr() as libc::c_ulong, 0, 0, 0, 0], Expect::Denied);
        policy.install_and_check(libc::SYS_socketcall, [2, bind_args.as_ptr() as libc::c_ulong, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}
