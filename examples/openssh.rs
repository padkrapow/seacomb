//! OpenSSH's filter for the pre-auth child of sshd,
//! [`preauth_insns`](https://github.com/openssh/openssh-portable/blob/V_10_5_P1/sandbox-seccomp-filter.c#L232).
//!
//! Gaps in our version:
//! - No kill on 32-bit arguments with junk upper 32 bits, which OpenSSH compares in full.
//! - On x86, `mmap` takes a pointer to its arguments, so it gets the default action.

#![recursion_limit = "256"]

#[cfg(not(target_os = "linux"))]
fn main() {}

#[cfg(target_os = "linux")]
fn main() {
    use seacomb::*;
    use std::os::unix::process::CommandExt;

    const SYS_GETSOCKNAME: i32 = 6;
    const SYS_GETPEERNAME: i32 = 7;
    const SYS_SHUTDOWN: i32 = 13;
    const SYS_GETSOCKOPT: i32 = 15;
    const FUTEX_CMD_MASK: i32 = !(libc::FUTEX_PRIVATE_FLAG | libc::FUTEX_CLOCK_REALTIME);
    const MMAP_FLAGS: i32 = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_FIXED | libc::MAP_FIXED_NOREPLACE;
    const MMAP_PROT: i32 = libc::PROT_READ | libc::PROT_WRITE | libc::PROT_NONE;

    let policy = policy! {
        default kill_thread on native;

        errno(libc::EACCES as u16) lstat();
        errno(libc::EACCES as u16) lstat64();
        errno(libc::EACCES as u16) fstat();
        errno(libc::EACCES as u16) fstat64();
        errno(libc::EACCES as u16) fstatat64();
        errno(libc::EACCES as u16) open();
        errno(libc::EACCES as u16) openat();
        errno(libc::EACCES as u16) newfstatat();
        errno(libc::EACCES as u16) stat();
        errno(libc::EACCES as u16) stat64();
        errno(libc::EACCES as u16) shmget();
        errno(libc::EACCES as u16) shmat();
        errno(libc::EACCES as u16) shmdt();
        errno(libc::EACCES as u16) ipc();
        errno(libc::EACCES as u16) statx();

        allow brk();
        allow clock_gettime();
        allow clock_gettime64();
        allow close();
        allow exit();
        allow exit_group();
        allow futex(_, op) if op & FUTEX_CMD_MASK == {libc::FUTEX_WAIT}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_WAIT_BITSET} || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE_BITSET} || op & FUTEX_CMD_MASK == {libc::FUTEX_REQUEUE}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_CMP_REQUEUE};
        [x86, arm] allow futex_time64(_, op) if op & FUTEX_CMD_MASK == {libc::FUTEX_WAIT}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_WAIT_BITSET} || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE_BITSET} || op & FUTEX_CMD_MASK == {libc::FUTEX_REQUEUE}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_CMP_REQUEUE};
        allow geteuid();
        allow geteuid32();
        allow getpgid();
        allow getpid();
        allow getrandom();
        allow gettid();
        allow gettimeofday();
        allow getuid();
        allow getuid32();
        allow madvise(_, _, advice) if advice == {libc::MADV_NORMAL} || advice == {libc::MADV_FREE}
            || advice == {libc::MADV_DONTNEED} || advice == {libc::MADV_DONTFORK} || advice == {libc::MADV_DONTDUMP}
            || advice == {libc::MADV_WIPEONFORK};
        errno(libc::EINVAL as u16) madvise(_, _, advice) if advice != {libc::MADV_NORMAL} && advice != {libc::MADV_FREE}
            && advice != {libc::MADV_DONTNEED} && advice != {libc::MADV_DONTFORK} && advice != {libc::MADV_DONTDUMP}
            && advice != {libc::MADV_WIPEONFORK};
        [x86_64, aarch64] errno(libc::EINVAL as u16) mmap(_, _, _, flags) if flags & {!MMAP_FLAGS} as usize != 0usize;
        [x86_64, aarch64] allow mmap(_, _, prot, flags)
            if flags & {!MMAP_FLAGS} as usize == 0usize && prot & {!MMAP_PROT} as usize == 0usize;
        [x86, arm] errno(libc::EINVAL as u16) mmap2(_, _, _, flags) if flags & {!MMAP_FLAGS} as usize != 0usize;
        [x86, arm] allow mmap2(_, _, prot, flags)
            if flags & {!MMAP_FLAGS} as usize == 0usize && prot & {!MMAP_PROT} as usize == 0usize;
        allow mprotect(_, _, prot) if prot & {!MMAP_PROT} as usize == 0usize;
        allow mremap();
        allow munmap();
        allow nanosleep();
        allow clock_nanosleep();
        allow clock_nanosleep_time64();
        allow _newselect();
        allow ppoll();
        allow ppoll_time64();
        allow poll();
        allow pselect6();
        allow pselect6_time64();
        allow read();
        allow rt_sigprocmask();
        allow select();
        allow exact shutdown();
        allow sigprocmask();
        allow time();
        allow write();
        allow writev();
        allow exact getsockopt();
        allow exact getsockname();
        allow exact getpeername();
        allow uname();
        allow exact setsockopt(_, level, optname) if level == {libc::IPPROTO_IPV6} && optname == {libc::IPV6_TCLASS}
            || level == {libc::IPPROTO_IP} && optname == {libc::IP_TOS};
        [x86] allow socketcall(call) if call == SYS_GETPEERNAME || call == SYS_GETSOCKNAME || call == SYS_GETSOCKOPT
            || call == SYS_SHUTDOWN;
        [x86] errno(libc::EACCES as u16) socketcall(call) if call != SYS_GETPEERNAME && call != SYS_GETSOCKNAME
            && call != SYS_GETSOCKOPT && call != SYS_SHUTDOWN;
    }.unwrap();

    policy.install().unwrap();
    let mut args = std::env::args_os().skip(1);
    if let Some(program) = args.next() {
        panic!("{}", std::process::Command::new(program).args(args).exec());
    }
}
