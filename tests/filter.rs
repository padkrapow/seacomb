//! Tests of the public `Filter` API.

use super::*;

/// Every action has the effect `seccomp(2)` gives it on a thread with no tracer or listener.
#[test]
fn actions() {
    for (action, expect) in [
        (Action::Allow, Expect::Ok),
        (Action::Log, Expect::Ok),
        (Action::Errno(4095), Expect::Errno(4095)),
        (Action::Trace(u16::MAX), Expect::Errno(libc::ENOSYS)),
        (Action::Notify, Expect::Errno(libc::ENOSYS)),
        (Action::Trap(u16::MAX), Expect::Sigsys),
        (Action::KillThread, Expect::Sigsys),
        (Action::KillProcess, Expect::Sigsys),
    ] {
        let filter = Filter::new_native_with_rule(Action::Allow, action, Syscall::Getpid, Cond::True).unwrap();
        unsafe { filter.install_and_check(libc::SYS_getpid, [0; 6], expect) };
    }
}

/// A native filter applies its default action to every syscall without a rule.
#[test]
fn default_action() {
    let mut filter = Filter::new_native(Expect::DENY).unwrap();
    filter.add_rule(Action::Allow, Syscall::Exit, Cond::True).unwrap();
    filter.add_rule(Action::Allow, Syscall::ExitGroup, Cond::True).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_getpid, [0; 6], Expect::Denied);
        filter.install_and_check(libc::SYS_getppid, [0; 6], Expect::Denied);
    }
}

/// A rejected update leaves the rules added before it in force.
#[test]
fn failed_add_keeps_rules() {
    let mut filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Getpid, Cond::True).unwrap();
    assert!(matches!(
        filter.add_arch(Arch::native().unwrap()),
        Err(Error::Check(CheckError::DuplicateArch))
    ));
    for (action, conds) in [
        (Action::Errno(4096), Cond::True),
        (Action::Errno(8), cond!({u32::MAX} == {u32::MAX})),
        (Action::Errno(8), cond!({0} == {0} && {6} == {6})),
    ] {
        assert!(filter.add_rule(action, Syscall::Getppid, conds).is_err());
    }
    unsafe {
        filter.install_and_check(libc::SYS_getpid, [0; 6], Expect::Denied);
        filter.install_and_check(libc::SYS_getppid, [0; 6], Expect::Ok);
    }
}

/// A rejected bad-architecture action leaves the one set before it in force.
#[test]
fn failed_bad_arch_keeps_action() {
    let mut filter = Filter::new(Action::Allow).unwrap();
    let absent = if Arch::native().unwrap() == Arch::X86 {
        Arch::Aarch64
    } else {
        Arch::X86
    };
    filter.add_arch(absent).unwrap();
    filter.on_bad_arch(Action::KillProcess).unwrap();
    assert!(matches!(
        filter.on_bad_arch(Action::Errno(4096)),
        Err(Error::Check(CheckError::InvalidErrno(_)))
    ));
    unsafe { filter.install_and_check(libc::SYS_getpid, [0; 6], Expect::Sigsys) };
}

/// An argument test narrows a rule to the calls that pass it.
#[test]
fn arg_eq() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Lseek, cond!({0} == 42 as u32)).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_lseek, [42, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_lseek, [43, 0, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// An argument test on a 64-bit architecture looks at both words of the argument.
#[cfg(target_pointer_width = "64")]
#[test]
fn arg_high_word() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Lseek, cond!({1} == 0x1_0000_0000 as iword)).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_lseek, [43, 0x1_0000_0000, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_lseek, [43, 1, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// A test on a 16-bit argument ignores the register bits above it.
#[test]
fn narrow_arg() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Fchmod, cond!({1} == 0o644 as u16)).unwrap();
    let fd = libc::c_ulong::MAX;
    unsafe {
        filter.install_and_check(libc::SYS_fchmod, [fd, 0o644, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_fchmod, [fd, 0x1_0000 | 0o644, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_fchmod, [fd, 0o645, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// An ordering test on a signed argument compares it as signed.
#[test]
fn signed_arg() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Ftruncate, cond!({1} < -1 as iword)).unwrap();
    let fd = libc::c_ulong::MAX;
    for (length, expect) in [
        (libc::c_long::MIN, Expect::Denied),
        (-2, Expect::Denied),
        (-1, Expect::Errno(libc::EINVAL)),
        (0, Expect::Errno(libc::EBADF)),
        (libc::c_long::MAX, Expect::Errno(libc::EBADF)),
    ] {
        unsafe { filter.install_and_check(libc::SYS_ftruncate, [fd, length as libc::c_ulong, 0, 0, 0, 0], expect) };
    }
}

/// A rule's argument tests must all hold, whatever order they were given in.
#[test]
fn six_conds() {
    let sig = Syscall::ProcessVmReadv.signature(Arch::native().unwrap());
    let &[t0, t1, t2, t3, t4, t5] = sig else { panic!("{sig:?}") };
    let cond = cond!({5} == 6 as t5 && {4} == 5 as t4 && {3} == 4 as t3 && {2} == 3 as t2 && {1} == 2 as t1 && {0} == 1 as t0);
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::ProcessVmReadv, cond).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_process_vm_readv, [1, 2, 3, 4, 5, 6], Expect::Denied);
        filter.install_and_check(libc::SYS_process_vm_readv, [2, 2, 3, 4, 5, 6], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_process_vm_readv, [1, 3, 3, 4, 5, 6], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_process_vm_readv, [1, 2, 4, 4, 5, 6], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_process_vm_readv, [1, 2, 3, 5, 5, 6], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_process_vm_readv, [1, 2, 3, 4, 6, 6], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_process_vm_readv, [1, 2, 3, 4, 5, 7], Expect::Errno(libc::EINVAL));
    }
}

/// Equality on a 64-bit argument checks both of its words.
#[cfg(target_pointer_width = "64")]
#[test]
fn eq_64() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::ProcessVmWritev, cond!({5} == 0x1_0000_0001 as uword)).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_process_vm_writev, [0, 0, 0, 0, 0, 0x1_0000_0001], Expect::Denied);
        filter.install_and_check(libc::SYS_process_vm_writev, [0, 0, 0, 0, 0, 1], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_process_vm_writev, [0, 0, 0, 0, 0, 0x1_0000_0000], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_process_vm_writev, [0, 0, 0, 0, 0, 0x2_0000_0001], Expect::Errno(libc::EINVAL));
    }
}

/// Inequality on a 64-bit argument holds when either word differs.
#[cfg(target_pointer_width = "64")]
#[test]
fn ne_64() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Munmap, cond!({0} != 0x1_0000_0001 as uword)).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_munmap, [0x1_0000_0001, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_munmap, [1, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_munmap, [0x1_0000_0000, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_munmap, [libc::c_ulong::MAX, 0, 0, 0, 0, 0], Expect::Denied);
    }
}

/// Less-than on a 64-bit argument compares across the word boundary.
#[cfg(target_pointer_width = "64")]
#[test]
fn lt_64() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Msync, cond!({1} < 0x1_0000_0001 as uword)).unwrap();
    let never = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Msync, cond!({1} < 0 as uword)).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_msync, [1, 0xffff_ffff, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_msync, [1, 0x1_0000_0000, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_msync, [1, 0x1_0000_0001, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_msync, [1, 0x2_0000_0000, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        never.install_and_check(libc::SYS_msync, [1, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        never.install_and_check(libc::SYS_msync, [1, libc::c_ulong::MAX, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
    }
}

/// Less-or-equal on a 64-bit argument includes its bound.
#[cfg(target_pointer_width = "64")]
#[test]
fn le_64() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Read, cond!({2} <= 0x1_0000_0000 as uword)).unwrap();
    let always = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Read, cond!({2} <= -1 as uword)).unwrap();
    let fd = libc::c_ulong::MAX;
    unsafe {
        filter.install_and_check(libc::SYS_read, [fd, 0, 0xffff_ffff, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_read, [fd, 0, 0x1_0000_0000, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_read, [fd, 0, 0x1_0000_0001, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_read, [fd, 0, 0x2_0000_0000, 0, 0, 0], Expect::Errno(libc::EBADF));
        always.install_and_check(libc::SYS_read, [fd, 0, 0, 0, 0, 0], Expect::Denied);
        always.install_and_check(libc::SYS_read, [fd, 0, libc::c_ulong::MAX, 0, 0, 0], Expect::Denied);
    }
}

/// Greater-than on a 64-bit argument compares across the word boundary.
#[cfg(target_pointer_width = "64")]
#[test]
fn gt_64() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Sendfile, cond!({3} > 0xffff_ffff as uword)).unwrap();
    let never = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Sendfile, cond!({3} > -1 as uword)).unwrap();
    let fd = libc::c_ulong::MAX;
    unsafe {
        filter.install_and_check(libc::SYS_sendfile, [fd, fd, 0, 0xffff_fffe, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_sendfile, [fd, fd, 0, 0xffff_ffff, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_sendfile, [fd, fd, 0, 0x1_0000_0000, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_sendfile, [fd, fd, 0, libc::c_ulong::MAX, 0, 0], Expect::Denied);
        never.install_and_check(libc::SYS_sendfile, [fd, fd, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        never.install_and_check(libc::SYS_sendfile, [fd, fd, 0, libc::c_ulong::MAX, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// Greater-or-equal on a 64-bit argument includes its bound.
#[cfg(target_pointer_width = "64")]
#[test]
fn ge_64() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Splice, cond!({4} >= 0x1_0000_0000 as uword)).unwrap();
    let always = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Splice, cond!({4} >= 0 as uword)).unwrap();
    let fd = libc::c_ulong::MAX;
    unsafe {
        filter.install_and_check(libc::SYS_splice, [fd, 0, fd, 0, 0xffff_ffff, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_splice, [fd, 0, fd, 0, 0x1_0000_0000, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_splice, [fd, 0, fd, 0, 0x1_0000_0001, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_splice, [fd, 0, fd, 0, 0x2_0000_0000, 0], Expect::Denied);
        always.install_and_check(libc::SYS_splice, [fd, 0, fd, 0, 0, 0], Expect::Denied);
        always.install_and_check(libc::SYS_splice, [fd, 0, fd, 0, libc::c_ulong::MAX, 0], Expect::Denied);
    }
}

/// Masked equality on a 64-bit argument masks and compares each word on its own.
#[cfg(target_pointer_width = "64")]
#[test]
fn masked_eq_64() {
    let cond = cond!({5} & 0xf0_0000_000f as uword == 0xa0_0000_0005 as uword);
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::EpollPwait, cond).unwrap();
    let cond = cond!({5} & 0xffff_ffff_0000_0000 as uword == 0x1_0000_0000 as uword);
    let high = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::EpollPwait, cond).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_epoll_pwait, [0, 0, 0, 0, 0, 0xa0_0000_0005], Expect::Denied);
        filter.install_and_check(libc::SYS_epoll_pwait, [0, 0, 0, 0, 0, 0xaf_ffff_fff5], Expect::Denied);
        filter.install_and_check(libc::SYS_epoll_pwait, [0, 0, 0, 0, 0, 0xb0_0000_0005], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_epoll_pwait, [0, 0, 0, 0, 0, 0xa0_0000_0006], Expect::Errno(libc::EINVAL));
        high.install_and_check(libc::SYS_epoll_pwait, [0, 0, 0, 0, 0, 0x1_0000_0000], Expect::Denied);
        high.install_and_check(libc::SYS_epoll_pwait, [0, 0, 0, 0, 0, 0x1_ffff_ffff], Expect::Denied);
        high.install_and_check(libc::SYS_epoll_pwait, [0, 0, 0, 0, 0, 0xffff_ffff], Expect::Errno(libc::EINVAL));
    }
}

/// Masked equality with a zero mask matches every value.
#[test]
fn zero_mask() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Mprotect, cond!({0} & 0 as uword == 0 as uword)).unwrap();
    unsafe {
        filter.install_and_check(libc::SYS_mprotect, [0, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_mprotect, [1, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_mprotect, [0x8000_0000, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_mprotect, [libc::c_ulong::MAX, 0, 0, 0, 0, 0], Expect::Denied);
    }
}

/// Ordering on an unsigned argument treats its top bit as a value bit rather than a sign.
#[test]
fn unsigned_arg() {
    let sign = (1 as libc::c_ulong) << (libc::c_ulong::BITS - 1);
    let policy_sign = 1u64 << (libc::c_ulong::BITS - 1);
    let below = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Write, cond!({2} < policy_sign as uword)).unwrap();
    let above = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Write, cond!({2} > policy_sign as uword)).unwrap();
    let fd = libc::c_ulong::MAX;
    unsafe {
        below.install_and_check(libc::SYS_write, [fd, 0, 0, 0, 0, 0], Expect::Denied);
        below.install_and_check(libc::SYS_write, [fd, 0, sign - 1, 0, 0, 0], Expect::Denied);
        below.install_and_check(libc::SYS_write, [fd, 0, sign, 0, 0, 0], Expect::Errno(libc::EBADF));
        below.install_and_check(libc::SYS_write, [fd, 0, libc::c_ulong::MAX, 0, 0, 0], Expect::Errno(libc::EBADF));
        above.install_and_check(libc::SYS_write, [fd, 0, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        above.install_and_check(libc::SYS_write, [fd, 0, sign - 1, 0, 0, 0], Expect::Errno(libc::EBADF));
        above.install_and_check(libc::SYS_write, [fd, 0, sign, 0, 0, 0], Expect::Errno(libc::EBADF));
        above.install_and_check(libc::SYS_write, [fd, 0, libc::c_ulong::MAX, 0, 0, 0], Expect::Denied);
    }
}

/// A filter without architectures is refused before anything is installed.
#[test]
fn no_arch() {
    let mut filter = Filter::new(Action::Allow).unwrap();
    filter.on_bad_arch(Action::KillProcess).unwrap();
    assert!(matches!(filter.install(), Err(Error::NoArch)));
}

/// On x86_64, an unmatched syscall takes the default action and an x32 one the bad-architecture action.
#[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
#[test]
fn x86_64_x32() {
    let mut filter = Filter::new_native(Expect::DENY).unwrap();
    filter.on_bad_arch(Action::Errno(libc::EPERM as u16)).unwrap();
    filter.add_rule(Action::Allow, Syscall::Exit, Cond::True).unwrap();
    filter.add_rule(Action::Allow, Syscall::ExitGroup, Cond::True).unwrap();
    let fd = libc::c_ulong::MAX;
    unsafe {
        filter.install_and_check(-1, [fd, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(-2, [fd, 0, 0, 0, 0, 0], Expect::Errno(libc::EPERM));
        filter.install_and_check(i32::MIN.into(), [fd, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(0x3fff_ffff, [fd, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(0x4000_0000, [fd, 0, 0, 0, 0, 0], Expect::Errno(libc::EPERM));
        filter.install_and_check(i32::MAX.into(), [fd, 0, 0, 0, 0, 0], Expect::Errno(libc::EPERM));
    }
}

/// On x86_64, a rule on `Syscall::Skip` matches syscall number -1 rather than the x32 action.
#[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
#[test]
fn x86_64_skip() {
    let mut filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Skip, Cond::True).unwrap();
    filter.on_bad_arch(Action::Errno(libc::EPERM as u16)).unwrap();
    unsafe { filter.install_and_check(-1, [0; 6], Expect::Denied) };
}

/// On x86, a socket rule covers both the direct call and its `socketcall` form.
#[cfg(target_arch = "x86")]
#[test]
fn x86_socketcall() {
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Socket, Cond::True).unwrap();
    let socket_args: [libc::c_ulong; 3] = [0; 3];
    let bind_args: [libc::c_ulong; 3] = [libc::c_ulong::MAX, 0, 0];
    unsafe {
        filter.install_and_check(libc::SYS_socket, [0; 6], Expect::Denied);
        filter.install_and_check(libc::SYS_socketcall, [1, socket_args.as_ptr() as libc::c_ulong, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_socketcall, [2, bind_args.as_ptr() as libc::c_ulong, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// On x86, an exact socket rule with conditions leaves `socketcall` alone.
#[cfg(target_arch = "x86")]
#[test]
fn x86_socketcall_exact_conds() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter.add_rule_exact(Expect::DENY, Syscall::Socket, cond!({0} == 1 as i32)).unwrap();
    let socket_args: [libc::c_ulong; 3] = [0; 3];
    unsafe {
        filter.install_and_check(libc::SYS_socket, [1, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_socket, [0; 6], Expect::Errno(libc::EAFNOSUPPORT));
        filter.install_and_check(libc::SYS_socketcall, [1, socket_args.as_ptr() as libc::c_ulong, 0, 0, 0, 0], Expect::Errno(libc::EAFNOSUPPORT));
    }
}

/// On x86, an exact socket rule without conditions still leaves `socketcall` alone.
#[cfg(target_arch = "x86")]
#[test]
fn x86_socketcall_exact() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter.add_rule_exact(Expect::DENY, Syscall::Socket, Cond::True).unwrap();
    let socket_args: [libc::c_ulong; 3] = [0; 3];
    unsafe {
        filter.install_and_check(libc::SYS_socket, [1, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_socketcall, [1, socket_args.as_ptr() as libc::c_ulong, 0, 0, 0, 0], Expect::Errno(libc::EAFNOSUPPORT));
    }
}

/// On x86, an IPC rule covers `ipc` whatever version bits its selector carries.
#[cfg(target_arch = "x86")]
#[test]
fn x86_ipc() {
    // The i386 semget number in `arch/x86/entry/syscalls/syscall_32.tbl`, which `libc` does not define.
    let semget: libc::c_long = 393;
    let filter = Filter::new_native_with_rule(Action::Allow, Expect::DENY, Syscall::Semget, Cond::True).unwrap();
    unsafe {
        filter.install_and_check(semget, [0; 6], Expect::Denied);
        filter.install_and_check(libc::SYS_ipc, [2, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_ipc, [0x1_0002, 0, 0, 0, 0, 0], Expect::Denied);
    }
}

/// On x86, an exact IPC rule leaves `ipc` alone.
#[cfg(target_arch = "x86")]
#[test]
fn x86_ipc_exact() {
    let semget: libc::c_long = 393;
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter.add_rule_exact(Expect::DENY, Syscall::Semget, Cond::True).unwrap();
    unsafe {
        filter.install_and_check(semget, [0; 6], Expect::Denied);
        filter.install_and_check(libc::SYS_ipc, [0x1_0002, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
    }
}

/// A rule on a syscall the native architecture lacks does not catch whatever has its number there.
#[cfg(target_arch = "aarch64")]
#[test]
fn aarch64_no_alias() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter.add_arch(Arch::X86_64).unwrap();
    filter.add_rule(Expect::DENY, Syscall::Open, Cond::True).unwrap();
    unsafe {
        // The x86_64 open number is io_submit on aarch64.
        filter.install_and_check(libc::SYS_io_submit, [0; 6], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_openat, [libc::c_ulong::MAX, 0, 0, 0, 0, 0], Expect::Errno(libc::EFAULT));
    }
}

/// A native filter already has the native architecture and takes every other one.
#[test]
fn new_native() {
    let mut filter = Filter::new_native(Action::Errno(7)).unwrap();
    let native = Arch::native().unwrap();
    assert!(matches!(filter.add_arch(native), Err(Error::Check(CheckError::DuplicateArch))));
    for arch in [Arch::X86, Arch::X86_64, Arch::Arm, Arch::Aarch64] {
        if arch != native {
            filter.add_arch(arch).unwrap();
        }
    }
    assert!(matches!(
        Filter::new_native(Action::Errno(4096)),
        Err(Error::Check(CheckError::InvalidErrno(_)))
    ));
}

/// Rules may repeat the default action's payload or use a different one.
#[test]
fn rule_payloads() {
    for (default, same, different) in [
        (Action::Errno(1), Action::Errno(1), Action::Errno(2)),
        (Action::Trace(0), Action::Trace(0), Action::Trace(u16::MAX)),
        (Action::Trap(0), Action::Trap(0), Action::Trap(u16::MAX)),
    ] {
        let mut filter = Filter::new_native(default).unwrap();
        filter.add_rule(same, Syscall::Getpid, Cond::True).unwrap();
        filter.add_rule(different, Syscall::Getpid, Cond::True).unwrap();
    }
}

/// Payloads up to each action's maximum are accepted, and errnos past 4095 are not.
#[test]
fn payload_limits() {
    for action in [
        Action::Errno(0),
        Action::Errno(4094),
        Action::Errno(4095),
        Action::Trace(u16::MAX),
        Action::Trap(u16::MAX),
    ] {
        Filter::new_native_with_rule(Action::Allow, action, Syscall::Getpid, Cond::True).unwrap();
    }
    for errno in [4096, u16::MAX] {
        assert!(matches!(
            Filter::new(Action::Errno(errno)),
            Err(Error::Check(CheckError::InvalidErrno(_)))
        ));
    }
}

/// Errno payloads above Linux's maximum are rejected rather than clamped.
#[test]
fn errno_limit() {
    assert!(Filter::new(Action::Errno(Action::MAX_ERRNO as u16 + 1)).is_err());
    assert!(Filter::new(Action::Errno(Action::MAX_ERRNO as u16)).is_ok());
}

/// The same architecture twice is turned down.
#[test]
fn duplicate_arch() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    assert!(filter.add_arch(Arch::native().unwrap()).is_err());
}

/// A rule that repeats the default action is allowed.
#[test]
fn repeat_default() {
    assert!(Filter::new_native_with_rule(Action::Allow, Action::Allow, Syscall::Getpid, Cond::True).is_ok());
}

/// An argument the architecture does not have is turned down.
#[test]
fn arg_out_of_range() {
    assert!(matches!(
        Filter::new_native_with_rule(Action::Allow, Action::Errno(1), Syscall::Lseek, cond!({6} == {6})),
        Err(Error::Check(CheckError::InvalidArg { given: 6, total: 3 })),
    ));
}

/// A rule on `Syscall::Skip` is allowed, but not with argument tests.
#[test]
fn skip_rule() {
    assert!(Filter::new_native_with_rule(Action::Allow, Action::Errno(1), Syscall::Skip, Cond::True).is_ok());
    assert!(matches!(
        Filter::new_native_with_rule(Action::Allow, Action::Errno(1), Syscall::Skip, cond!({0} == {0})),
        Err(Error::Check(CheckError::InvalidArg { given: 0, total: 0 })),
    ));
}

/// A syscall without arguments takes no argument tests.
#[test]
fn no_args() {
    assert!(matches!(
        Filter::new_native_with_rule(Action::Allow, Action::Errno(1), Syscall::Getpid, cond!({0} == {0})),
        Err(Error::Check(CheckError::InvalidArg { given: 0, total: 0 })),
    ));
}

/// A rejected argument test reports the operator and the types it was given.
#[test]
fn arg_type_errors() {
    assert!(matches!(
        Filter::new_native_with_rule(Action::Allow, Action::Errno(1), Syscall::Fchmodat, cond!({1} < 0 as ptr)),
        Err(Error::Check(CheckError::CmpTypes { op: CmpOp::Lt, lhs: Ptr, rhs: Ptr, .. })),
    ));
    assert!(matches!(
        Filter::new_native_with_rule(Action::Allow, Action::Errno(1), Syscall::Fchmod, cond!({1} == 1 as i16)),
        Err(Error::Check(CheckError::CmpTypes { op: CmpOp::Eq, lhs: U(16), rhs: I(16) })),
    ));
    let masked = cond!({1} & 0x1_0000 as u32 == 0 as u16);
    assert!(matches!(
        Filter::new_native_with_rule(Action::Allow, Action::Errno(1), Syscall::Fchmod, masked),
        Err(Error::Check(CheckError::BinOpTypes { op: BinOp::And, lhs: U(16), rhs: U(32), .. })),
    ));
}

/// A `u32` constant fits an `off_t` argument only where the word is wider than 32 bits.
#[test]
fn word_literal() {
    let result = Filter::new_native_with_rule(Action::Allow, Action::Errno(1), Syscall::Lseek, cond!({1} == 1 as u32));
    if cfg!(target_pointer_width = "64") {
        assert!(result.is_ok());
    } else {
        assert!(matches!(result, Err(Error::Check(CheckError::CmpTypes { lhs: IWord, rhs: U(32), .. }))));
    }
}

/// Errno 0 makes the syscall succeed without running, and errnos up to 4095 come back as given.
#[test]
fn errno_edges() {
    for (errno, expect) in [(0, Expect::Ok), (4094, Expect::Errno(4094)), (4095, Expect::Errno(4095))] {
        let filter = Filter::new_native_with_rule(Action::Allow, Action::Errno(errno), Syscall::Lseek, Cond::True).unwrap();
        unsafe { filter.install_and_check(libc::SYS_lseek, [libc::c_ulong::MAX, 0, 0, 0, 0, 0], expect) };
    }
}

/// A chain of rules long enough to need far jumps still matches each rule and falls through past them.
#[test]
fn long_chain() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    for count in 0..300 {
        filter.add_rule(Expect::DENY, Syscall::Read, cond!({2} == count as uword)).unwrap();
    }
    let fd = libc::c_ulong::MAX;
    unsafe {
        filter.install_and_check(libc::SYS_read, [fd, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_read, [fd, 0, 150, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_read, [fd, 0, 299, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_read, [fd, 0, 300, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_getppid, [0; 6], Expect::Ok);
    }
}

/// A filter over the kernel's 4096-instruction limit is refused before anything is installed.
#[test]
fn too_large() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    for count in 0..4096 {
        filter.add_rule(Expect::DENY, Syscall::Read, cond!({2} == count as uword)).unwrap();
    }
    let before = unsafe { libc::prctl(libc::PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) };
    assert!(matches!(filter.install(), Err(Error::FilterTooLarge)));
    assert_eq!(unsafe { libc::prctl(libc::PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) }, before);
}
