//! Firefox's filter for a content process,
//! [`ContentSandboxPolicy`](https://github.com/mozilla-firefox/firefox/blob/0813a05915398fda05345d5efded3504d96df558/security/sandbox/linux/SandboxFilter.cpp#L1437)
//! (assuming Firefox's defaults on Linux).
//!
//! Gaps: same as `examples/chrome.rs`.

#![recursion_limit = "512"]

#[cfg(not(target_os = "linux"))]
fn main() {}

#[cfg(target_os = "linux")]
fn main() {
    use seacomb::*;
    use std::os::unix::process::CommandExt;

    const BLOCKED_SYSCALL_TRAP: u16 = 1;
    const PANIC_INVALID_ARCH: u16 = 2;
    const PANIC_ABI_MIXING: u16 = 3;
    const GET_PPID_TRAP: u16 = 4;
    const UNEXPECTED_64BIT_ARG3: u16 = 5;
    const UNEXPECTED_64BIT_ARG0: u16 = 6;
    const OPEN_TRAP: u16 = 7;
    const ACCESS_TRAP: u16 = 8;
    const STAT_TRAP: u16 = 9;
    const LSTAT_TRAP: u16 = 10;
    const CHMOD_TRAP: u16 = 11;
    const LINK_TRAP: u16 = 12;
    const MKDIR_TRAP: u16 = 13;
    const RENAME_TRAP: u16 = 14;
    const RMDIR_TRAP: u16 = 15;
    const UNLINK_TRAP: u16 = 16;
    const READLINK_TRAP: u16 = 17;
    const OPEN_AT_TRAP: u16 = 18;
    const ACCESS_AT_TRAP: u16 = 19;
    const ACCESS_AT2_TRAP: u16 = 20;
    const STAT_AT_TRAP: u16 = 21;
    const CHMOD_AT_TRAP: u16 = 22;
    const LINK_AT_TRAP: u16 = 23;
    const MKDIR_AT_TRAP: u16 = 24;
    const RENAME_AT_TRAP: u16 = 25;
    const UNLINK_AT_TRAP: u16 = 26;
    const READLINK_AT_TRAP: u16 = 27;
    const TKILL_COMPAT_TRAP: u16 = 28;
    const STAT_FS_TRAP: u16 = 29;
    const FAKE_SOCKET_TRAP: u16 = 30;
    const CONNECT_TRAP: u16 = 31;
    const SOCKETPAIR_DATAGRAM_TRAP: u16 = 32;

    const UPPER_HALF: u64 = 0xffff_ffff_0000_0000;
    const SIGN_EXTENDED: u64 = 0xffff_ffff_8000_0000;

    const O_LARGEFILE_REAL: i32 = 0o100000;
    const FMODE_NONOTIFY: i32 = 0x4000000;
    const F_DUPFD_QUERY: i32 = 1024 + 3;
    const CPUCLOCK_PERTHREAD_MASK: i32 = 4;
    const CPUCLOCK_SCHED: i32 = 2;
    const ARCH_SET_GS: i32 = 0x1001;
    const KCMP_FILE: i32 = 0;

    match Arch::native().unwrap() {
        Arch::X86_64 | Arch::Aarch64 => {}
        _ => unimplemented!(),
    }

    let my_pid = std::process::id() as i32;
    let this_process = !my_pid << 3 | CPUCLOCK_SCHED;
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;

    let policy = policy! {
        default trap(BLOCKED_SYSCALL_TRAP) on native else trap(PANIC_INVALID_ARCH);

        [x86_64] trap(PANIC_ABI_MIXING) skip();

        trap(GET_PPID_TRAP) getppid();

        allow fstatfs();
        allow flock();

        [x86_64] errno(libc::EPERM as u16) mknod(_, mode) if mode & {libc::S_IFMT} as u16 == {libc::S_IFCHR} as u16;
        errno(libc::EPERM as u16) mknodat(_, _, mode) if mode & {libc::S_IFMT} as u16 == {libc::S_IFCHR} as u16;
        errno(libc::EPERM as u16) chown();
        errno(libc::EPERM as u16) fchownat();

        allow select();
        allow pselect6();

        allow writev();
        allow pwrite64();
        allow readahead();

        allow ioctl(_, request) if request == {libc::FIOCLEX} as u32 || request == {libc::FIONBIO} as u32;
        errno(libc::ENOTTY as u16) ioctl(_, request) if request == {libc::TCGETS} as u32
            || request == {libc::TIOCGWINSZ} as u32 || request == {libc::TCGETS2} as u32;

        allow fcntl(_, cmd) if cmd == {libc::F_SETLK} as u32 || cmd == {libc::F_SETLKW} as u32
            || cmd == {libc::F_ADD_SEALS} as u32 || cmd == {libc::F_GET_SEALS} as u32
            || cmd == {libc::F_GETFD} as u32 || cmd == {libc::F_GETFL} as u32
            || cmd == {libc::F_DUPFD_CLOEXEC} as u32 || cmd == {F_DUPFD_QUERY} as u32;
        allow fcntl(_, cmd, flags) if cmd == {libc::F_SETFD} as u32
            && flags as u32 & {!libc::FD_CLOEXEC} as u32 == 0u32;
        allow fcntl(_, cmd, flags) if cmd == {libc::F_SETFL} as u32
            && flags as u32 & {!(libc::O_ACCMODE | O_LARGEFILE_REAL | libc::O_CLOEXEC | FMODE_NONOTIFY
                | libc::O_APPEND | libc::O_NONBLOCK)} as u32 == 0u32;

        allow brk();
        allow madvise();

        allow mremap(_, _, _, flags) if flags as u32 == 0u32;
        trap(UNEXPECTED_64BIT_ARG3) mremap(_, _, _, flags)
            if flags & {UPPER_HALF} as usize != 0usize && flags & {SIGN_EXTENDED} as usize != {SIGN_EXTENDED} as usize;

        allow mincore(_, length) if length == {page_size};

        allow set_thread_area();

        allow getrusage();
        allow times();

        allow fsync();
        allow msync();

        allow getpriority();
        allow setpriority();
        allow sched_getattr();
        allow sched_setattr();
        allow sched_get_priority_min();
        allow sched_get_priority_max();
        allow sched_getscheduler();
        allow sched_setscheduler();
        allow sched_getparam();
        allow sched_setparam();
        allow sched_getaffinity();

        errno(libc::EPERM as u16) sched_setaffinity();

        allow pipe2(_, flags) if flags & {!(libc::O_CLOEXEC | libc::O_NONBLOCK | libc::O_DIRECT)} == 0;

        allow getrlimit();
        allow getresuid();
        allow getresgid();

        allow prlimit64(pid, _, new_limit) if pid == 0 && new_limit == 0usize as ptr;

        errno(libc::ECHILD as u16) wait4();

        allow eventfd2();

        allow rt_tgsigqueueinfo(tgid) if tgid == {my_pid};

        allow mlock();
        allow munlock();

        allow clone(flags) if flags as u32 & {!libc::CLONE_DETACHED} as u32 == {libc::CLONE_VM | libc::CLONE_FS
            | libc::CLONE_FILES | libc::CLONE_SIGHAND | libc::CLONE_THREAD | libc::CLONE_SYSVSEM | libc::CLONE_SETTLS
            | libc::CLONE_PARENT_SETTID | libc::CLONE_CHILD_CLEARTID} as u32;
        errno(libc::EPERM as u16) clone(flags) if flags as u32 & {!libc::CLONE_DETACHED} as u32 != {libc::CLONE_VM
            | libc::CLONE_FS | libc::CLONE_FILES | libc::CLONE_SIGHAND | libc::CLONE_THREAD | libc::CLONE_SYSVSEM
            | libc::CLONE_SETTLS | libc::CLONE_PARENT_SETTID | libc::CLONE_CHILD_CLEARTID} as u32;
        trap(UNEXPECTED_64BIT_ARG0) clone(flags)
            if flags & {UPPER_HALF} as usize != 0usize && flags & {SIGN_EXTENDED} as usize != {SIGN_EXTENDED} as usize;
        errno(libc::ENOSYS as u16) fork();

        allow fadvise64();
        allow fallocate();
        allow get_mempolicy();
        errno(libc::ENOSYS as u16) set_mempolicy();

        allow kcmp(pid1, pid2, kind) if pid1 == {my_pid} && pid2 == {my_pid} && kind == KCMP_FILE;

        allow sysinfo();

        trap(OPEN_TRAP) open();
        trap(ACCESS_TRAP) access();
        trap(STAT_TRAP) stat();
        trap(LSTAT_TRAP) lstat();
        trap(CHMOD_TRAP) chmod();
        trap(LINK_TRAP) link();
        trap(MKDIR_TRAP) mkdir();
        errno(libc::EPERM as u16) symlink();
        trap(RENAME_TRAP) rename();
        trap(RMDIR_TRAP) rmdir();
        trap(UNLINK_TRAP) unlink();
        trap(READLINK_TRAP) readlink();

        trap(OPEN_AT_TRAP) openat();
        trap(ACCESS_AT_TRAP) faccessat();
        trap(ACCESS_AT2_TRAP) faccessat2();
        trap(STAT_AT_TRAP) newfstatat();
        errno(libc::ENOSYS as u16) statx();
        trap(CHMOD_AT_TRAP) fchmodat();
        trap(LINK_AT_TRAP) linkat();
        trap(MKDIR_AT_TRAP) mkdirat();
        errno(libc::EPERM as u16) symlinkat();
        trap(RENAME_AT_TRAP) renameat();
        trap(UNLINK_AT_TRAP) unlinkat();
        trap(READLINK_AT_TRAP) readlinkat();

        allow gettimeofday();
        allow time();
        allow nanosleep();

        allow clock_gettime(clk_id) if clk_id == {libc::CLOCK_MONOTONIC} || clk_id == {libc::CLOCK_MONOTONIC_COARSE}
            || clk_id == {libc::CLOCK_MONOTONIC_RAW} || clk_id == {libc::CLOCK_PROCESS_CPUTIME_ID}
            || clk_id == {libc::CLOCK_REALTIME} || clk_id == {libc::CLOCK_REALTIME_COARSE}
            || clk_id == {libc::CLOCK_THREAD_CPUTIME_ID} || clk_id == {this_process}
            || clk_id & 7 == {CPUCLOCK_PERTHREAD_MASK | CPUCLOCK_SCHED} || clk_id == {libc::CLOCK_BOOTTIME};
        allow clock_getres(clk_id) if clk_id == {libc::CLOCK_MONOTONIC} || clk_id == {libc::CLOCK_MONOTONIC_COARSE}
            || clk_id == {libc::CLOCK_MONOTONIC_RAW} || clk_id == {libc::CLOCK_PROCESS_CPUTIME_ID}
            || clk_id == {libc::CLOCK_REALTIME} || clk_id == {libc::CLOCK_REALTIME_COARSE}
            || clk_id == {libc::CLOCK_THREAD_CPUTIME_ID} || clk_id == {this_process}
            || clk_id & 7 == {CPUCLOCK_PERTHREAD_MASK | CPUCLOCK_SCHED} || clk_id == {libc::CLOCK_BOOTTIME};
        allow clock_nanosleep(clk_id) if clk_id == {libc::CLOCK_MONOTONIC} || clk_id == {libc::CLOCK_MONOTONIC_COARSE}
            || clk_id == {libc::CLOCK_MONOTONIC_RAW} || clk_id == {libc::CLOCK_PROCESS_CPUTIME_ID}
            || clk_id == {libc::CLOCK_REALTIME} || clk_id == {libc::CLOCK_REALTIME_COARSE}
            || clk_id == {libc::CLOCK_THREAD_CPUTIME_ID} || clk_id == {this_process}
            || clk_id & 7 == {CPUCLOCK_PERTHREAD_MASK | CPUCLOCK_SCHED} || clk_id == {libc::CLOCK_BOOTTIME};

        allow futex();

        allow epoll_create();
        allow epoll_create1();
        allow epoll_wait();
        allow epoll_pwait();
        allow epoll_pwait2();
        allow epoll_ctl();
        allow poll();
        allow ppoll();

        allow pipe();

        allow fstat();

        allow pread64();
        allow write();
        allow read();
        allow readv();
        allow lseek();

        allow getdents();
        allow getdents64();

        allow ftruncate();

        allow dup();

        allow mmap(_, _, _, flags)
            if flags as u32 & {libc::MAP_HUGETLB | libc::MAP_HUGE_MASK << libc::MAP_HUGE_SHIFT} as u32 == 0u32;
        errno(libc::ENOSYS as u16) mmap(_, _, _, flags)
            if flags as u32 & {libc::MAP_HUGETLB | libc::MAP_HUGE_MASK << libc::MAP_HUGE_SHIFT} as u32 != 0u32;
        trap(UNEXPECTED_64BIT_ARG3) mmap(_, _, _, flags)
            if flags & {UPPER_HALF} as usize != 0usize && flags & {SIGN_EXTENDED} as usize != {SIGN_EXTENDED} as usize;
        allow munmap();

        allow memfd_create(_, flags)
            if flags & {libc::MFD_HUGETLB | libc::MFD_HUGE_MASK << libc::MFD_HUGE_SHIFT} == 0u32;
        errno(libc::ENOSYS as u16) memfd_create(_, flags)
            if flags & {libc::MFD_HUGETLB | libc::MFD_HUGE_MASK << libc::MFD_HUGE_SHIFT} != 0u32;

        allow mprotect();

        allow membarrier();

        allow sigaltstack();
        allow rt_sigreturn();
        allow rt_sigprocmask();
        allow rt_sigaction();

        allow tgkill(tgid) if tgid == {my_pid};
        trap(TKILL_COMPAT_TRAP) tkill();

        allow sched_yield();

        errno(libc::ENOSYS as u16) clone3();

        allow set_robust_list();

        allow prctl(option, arg2) if option == {libc::PR_SET_VMA} && arg2 as u32 == {libc::PR_SET_VMA_ANON_NAME} as u32;
        allow prctl(option) if option == {libc::PR_GET_SECCOMP} || option == {libc::PR_SET_NAME}
            || option == {libc::PR_SET_DUMPABLE} || option == {libc::PR_SET_PTRACER};
        errno(libc::EINVAL as u16) prctl(option) if option == {libc::PR_CAPBSET_READ};

        [x86_64] allow arch_prctl(code) if code == ARCH_SET_GS;

        allow getcpu();

        allow getpid();
        allow gettid();

        allow close();

        allow restart_syscall();

        allow exit();
        allow exit_group();

        allow getrandom();

        allow getuid();
        allow getgid();
        allow geteuid();
        allow getegid();

        allow rseq();

        allow dup2();
        allow dup3();

        trap(STAT_FS_TRAP) statfs();

        errno(libc::ENOENT as u16) getcwd();

        allow uname();

        trap(FAKE_SOCKET_TRAP) socket();
        trap(CONNECT_TRAP) connect();

        allow getsockopt();
        allow setsockopt();
        allow getsockname();
        allow getpeername();
        allow shutdown();

        allow exact socketpair(domain, kind) if domain == {libc::AF_UNIX}
            && (kind & {!(libc::SOCK_CLOEXEC | libc::SOCK_NONBLOCK)} == {libc::SOCK_STREAM}
            || kind & {!(libc::SOCK_CLOEXEC | libc::SOCK_NONBLOCK)} == {libc::SOCK_SEQPACKET});
        trap(SOCKETPAIR_DATAGRAM_TRAP) exact socketpair(domain, kind) if domain == {libc::AF_UNIX}
            && kind & {!(libc::SOCK_CLOEXEC | libc::SOCK_NONBLOCK)} == {libc::SOCK_DGRAM};

        allow exact sendto(_, _, _, flags) if flags & {!(libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL
            | libc::MSG_CMSG_CLOEXEC | libc::MSG_PEEK | libc::MSG_WAITALL | libc::MSG_TRUNC)} as u32 == 0u32;
        allow exact recvfrom(_, _, _, flags) if flags & {!(libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL
            | libc::MSG_CMSG_CLOEXEC | libc::MSG_PEEK | libc::MSG_WAITALL | libc::MSG_TRUNC)} as u32 == 0u32;
        allow exact sendmsg(_, _, flags) if flags & {!(libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL
            | libc::MSG_CMSG_CLOEXEC | libc::MSG_PEEK | libc::MSG_WAITALL | libc::MSG_TRUNC)} as u32 == 0u32;
        allow exact recvmsg(_, _, flags) if flags & {!(libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL
            | libc::MSG_CMSG_CLOEXEC | libc::MSG_PEEK | libc::MSG_WAITALL | libc::MSG_TRUNC)} as u32 == 0u32;

        errno(libc::EPERM as u16) shmget();
    }.unwrap();

    policy.install().unwrap();
    let mut args = std::env::args_os().skip(1);
    if let Some(program) = args.next() {
        panic!("{}", std::process::Command::new(program).args(args).exec());
    }
}
