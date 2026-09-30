//! Models Chromium's renderer filter,
//! [`RendererProcessPolicy`](https://github.com/chromium/chromium/blob/53e4d45264e5f16bf8bbcb0a755a5c5e93a2c564/sandbox/policy/linux/bpf_renderer_policy_linux.cc)
//! over [`BaselinePolicy`](https://github.com/chromium/chromium/blob/53e4d45264e5f16bf8bbcb0a755a5c5e93a2c564/sandbox/linux/seccomp-bpf-helpers/baseline_policy.cc),
//! for a Linux desktop build on x86-64 or AArch64.
//!
//! Gaps in our version:
//! - No trap (`Unexpected64bitArgument`) on 32-bit arguments with junk upper 32 bits.
//! - For `ioctl`, we only compare the low 32 bits of the request, where Chromium compares an `unsigned long`.
//! - An x32 syscall gets the `PANIC_INVALID_ARCH` trap instead of `PANIC_ABI_MIXING`.

#![recursion_limit = "1024"]

#[cfg(not(target_os = "linux"))]
fn main() {}

#[cfg(target_os = "linux")]
fn main() {
    use seacomb::*;
    use std::os::unix::process::CommandExt;

    const CRASH_SIGSYS: u16 = 1;
    const SIGSYS_IOCTL_FAILURE: u16 = 2;
    const SIGSYS_PRCTL_FAILURE: u16 = 3;
    const SIGSYS_CLONE_FAILURE: u16 = 4;
    const SIGSYS_FUTEX_FAILURE: u16 = 5;
    const SIGSYS_SCHED_HANDLER: u16 = 6;
    const SIGSYS_KILL_FAILURE: u16 = 7;
    const SIGSYS_FSTATAT_HANDLER: u16 = 8;
    const UNEXPECTED_64BIT: u16 = 9;
    const PANIC_ABI_MIXING: u16 = 10;
    const PANIC_INVALID_ARCH: u16 = 11;

    const DMA_BUF_IOCTL_SYNC: u32 = 0x4008_6200;
    const PR_SVE_GET_VL: i32 = 51;
    const PR_SME_GET_VL: i32 = 64;
    const PR_SET_VMA: i32 = 0x5356_4d41;
    const PR_SET_VMA_ANON_NAME: i32 = 0;
    const MAP_DROPPABLE: i32 = 0x08;
    const PROT_BTI: i32 = 0x10;
    const PROT_MTE: i32 = 0x20;
    const STATX_BASIC_STATS: u32 = 0x07ff;
    const FUTEX_CMD_MASK: i32 = !(libc::FUTEX_PRIVATE_FLAG | libc::FUTEX_CLOCK_REALTIME);
    const UPPER_HALF: u64 = 0xffff_ffff_0000_0000;
    const SIGN_EXTENDED: u64 = 0xffff_ffff_8000_0000;

    let (o_largefile, prot_arch) = match Arch::native().unwrap() {
        Arch::X86_64 => (0o100000, 0),
        Arch::Aarch64 => (0, PROT_MTE | PROT_BTI),
        _ => unimplemented!(),
    };
    let policy_pid = std::process::id() as i32;

    let policy = policy! {
        default trap(CRASH_SIGSYS) on native else trap(PANIC_INVALID_ARCH);

        allow clock_getres(clockid) if clockid == {libc::CLOCK_BOOTTIME} || clockid == {libc::CLOCK_MONOTONIC}
            || clockid == {libc::CLOCK_MONOTONIC_COARSE} || clockid == {libc::CLOCK_MONOTONIC_RAW}
            || clockid == {libc::CLOCK_PROCESS_CPUTIME_ID} || clockid == {libc::CLOCK_REALTIME}
            || clockid == {libc::CLOCK_REALTIME_COARSE} || clockid == {libc::CLOCK_THREAD_CPUTIME_ID};

        allow ioctl(_, request)
            if request == {libc::TCGETS} as u32 || request == {libc::FIONREAD} as u32 || request == DMA_BUF_IOCTL_SYNC;
        trap(SIGSYS_IOCTL_FAILURE) ioctl(_, request)
            if request != {libc::TCGETS} as u32 && request != {libc::FIONREAD} as u32 && request != DMA_BUF_IOCTL_SYNC;

        allow fdatasync();
        allow fsync();
        allow ftruncate();
        allow getrlimit();
        allow setrlimit();
        allow mremap();
        allow pwrite64();
        allow sched_get_priority_max();
        allow sched_get_priority_min();
        allow sysinfo();
        allow times();
        allow uname();
        [aarch64] allow getcpu();

        [aarch64] allow prctl(option) if option == PR_SVE_GET_VL || option == PR_SME_GET_VL;

        allow prlimit64(pid) if pid == 0 || pid == {policy_pid};
        errno(libc::EPERM as u16) prlimit64(pid) if pid != 0 && pid != {policy_pid};

        allow set_robust_list();

        errno(libc::EPERM as u16) sendfile();

        allow brk();
        allow mlock();
        allow munlock();
        allow munmap();
        allow mseal();

        allow sched_yield();
        allow pause();
        allow nanosleep();

        allow epoll_create();
        allow epoll_wait();
        allow epoll_pwait();
        allow epoll_create1();
        allow epoll_ctl();

        allow eventfd();
        allow eventfd2();

        allow fstat();

        allow lseek();
        allow poll();
        allow ppoll();
        allow pselect6();
        allow read();
        allow readv();
        allow pread64();
        allow recvfrom();
        allow recvmsg();
        allow recvmmsg();
        allow select();
        allow write();
        allow writev();

        allow gettimeofday();
        allow time();

        allow exit();
        allow exit_group();
        allow wait4();
        allow waitid();

        allow rt_sigaction();
        allow rt_sigprocmask();
        allow rt_sigreturn();
        allow rt_sigtimedwait();
        allow sigaltstack();

        allow capget();
        allow getegid();
        allow geteuid();
        allow getgid();
        allow getgroups();
        allow getpid();
        allow getppid();
        allow getresgid();
        allow getsid();
        allow gettid();
        allow getuid();
        allow getresuid();

        allow restart_syscall();

        allow close();
        allow dup();
        allow dup2();
        allow dup3();
        allow shutdown();

        allow exact sendmsg(_, _, flags) if flags & {!(libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL)} as u32 == 0u32;
        allow exact sendto(_, _, _, flags) if flags & {!(libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL)} as u32 == 0u32;

        allow rseq();

        allow pkey_alloc(flags) if flags as u32 == 0u32;
        allow pkey_free();

        allow clock_gettime(clockid) if clockid == {libc::CLOCK_BOOTTIME} || clockid == {libc::CLOCK_MONOTONIC}
            || clockid == {libc::CLOCK_MONOTONIC_COARSE} || clockid == {libc::CLOCK_MONOTONIC_RAW}
            || clockid == {libc::CLOCK_PROCESS_CPUTIME_ID} || clockid == {libc::CLOCK_REALTIME}
            || clockid == {libc::CLOCK_REALTIME_COARSE} || clockid == {libc::CLOCK_THREAD_CPUTIME_ID};
        allow clock_nanosleep(clockid) if clockid == {libc::CLOCK_BOOTTIME} || clockid == {libc::CLOCK_MONOTONIC}
            || clockid == {libc::CLOCK_MONOTONIC_COARSE} || clockid == {libc::CLOCK_MONOTONIC_RAW}
            || clockid == {libc::CLOCK_PROCESS_CPUTIME_ID} || clockid == {libc::CLOCK_REALTIME}
            || clockid == {libc::CLOCK_REALTIME_COARSE} || clockid == {libc::CLOCK_THREAD_CPUTIME_ID};

        allow clone(flags) if flags == {libc::CLONE_VM | libc::CLONE_FS | libc::CLONE_FILES | libc::CLONE_SIGHAND
            | libc::CLONE_THREAD | libc::CLONE_SYSVSEM | libc::CLONE_SETTLS | libc::CLONE_PARENT_SETTID
            | libc::CLONE_CHILD_CLEARTID} as usize;
        errno(libc::EPERM as u16) clone(flags) if flags & {libc::CLONE_VM | libc::CLONE_THREAD} as usize == 0usize
            || flags & {libc::CLONE_VFORK | libc::CLONE_VM} as usize == {libc::CLONE_VFORK | libc::CLONE_VM} as usize;
        trap(SIGSYS_CLONE_FAILURE) clone(flags) if flags != {libc::CLONE_VM | libc::CLONE_FS | libc::CLONE_FILES
            | libc::CLONE_SIGHAND | libc::CLONE_THREAD | libc::CLONE_SYSVSEM | libc::CLONE_SETTLS
            | libc::CLONE_PARENT_SETTID | libc::CLONE_CHILD_CLEARTID} as usize
            && flags & {libc::CLONE_VM | libc::CLONE_THREAD} as usize != 0usize
            && flags & {libc::CLONE_VFORK | libc::CLONE_VM} as usize != {libc::CLONE_VFORK | libc::CLONE_VM} as usize;

        errno(libc::ENOSYS as u16) clone3();

        errno(libc::ENOSYS as u16) pidfd_open();

        allow fcntl(_, cmd) if cmd == {libc::F_GETFL} as u32 || cmd == {libc::F_GETFD} as u32
            || cmd == {libc::F_GET_SEALS} as u32 || cmd == {libc::F_SETFD} as u32 || cmd == {libc::F_SETLK} as u32
            || cmd == {libc::F_SETLKW} as u32 || cmd == {libc::F_GETLK} as u32 || cmd == {libc::F_DUPFD} as u32
            || cmd == {libc::F_DUPFD_CLOEXEC} as u32;
        allow fcntl(_, cmd, arg) if cmd == {libc::F_SETFL} as u32
            && arg & {!(libc::O_ACCMODE | libc::O_APPEND | libc::O_NONBLOCK | libc::O_SYNC | o_largefile
                | libc::O_CLOEXEC | libc::O_NOATIME)} as usize == 0usize;
        allow fcntl(_, cmd, arg) if cmd == {libc::F_ADD_SEALS} as u32
            && arg & {!(libc::F_SEAL_SEAL | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK)} as usize == 0usize;

        errno(libc::EPERM as u16) fork();

        errno(libc::EPERM as u16) vfork();

        allow futex(_, op) if op & FUTEX_CMD_MASK == {libc::FUTEX_WAIT} || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_REQUEUE} || op & FUTEX_CMD_MASK == {libc::FUTEX_CMP_REQUEUE}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE_OP} || op & FUTEX_CMD_MASK == {libc::FUTEX_WAIT_BITSET}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE_BITSET};
        trap(SIGSYS_FUTEX_FAILURE) futex(_, op) if !(op & FUTEX_CMD_MASK == {libc::FUTEX_WAIT}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE} || op & FUTEX_CMD_MASK == {libc::FUTEX_REQUEUE}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_CMP_REQUEUE} || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE_OP}
            || op & FUTEX_CMD_MASK == {libc::FUTEX_WAIT_BITSET} || op & FUTEX_CMD_MASK == {libc::FUTEX_WAKE_BITSET});

        allow getpriority(which, who) if which == {libc::PRIO_PROCESS} as i32 && (who == 0 || who == {policy_pid});
        errno(libc::EPERM as u16) getpriority(which, who)
            if which == {libc::PRIO_PROCESS} as i32 && who != 0 && who != {policy_pid};
        allow setpriority(which, who) if which == {libc::PRIO_PROCESS} as i32 && (who == 0 || who == {policy_pid});
        errno(libc::EPERM as u16) setpriority(which, who)
            if which == {libc::PRIO_PROCESS} as i32 && who != 0 && who != {policy_pid};

        allow sched_getaffinity(pid) if pid == 0 || pid == {policy_pid};
        trap(SIGSYS_SCHED_HANDLER) sched_getaffinity(pid) if pid != 0 && pid != {policy_pid};
        allow sched_getparam(pid) if pid == 0 || pid == {policy_pid};
        trap(SIGSYS_SCHED_HANDLER) sched_getparam(pid) if pid != 0 && pid != {policy_pid};
        allow sched_getscheduler(pid) if pid == 0 || pid == {policy_pid};
        trap(SIGSYS_SCHED_HANDLER) sched_getscheduler(pid) if pid != 0 && pid != {policy_pid};
        allow sched_setscheduler(pid) if pid == 0 || pid == {policy_pid};
        trap(SIGSYS_SCHED_HANDLER) sched_setscheduler(pid) if pid != 0 && pid != {policy_pid};

        allow getrandom(_, _, flags) if flags & {!(libc::GRND_NONBLOCK | libc::GRND_INSECURE)} == 0u32;

        allow madvise(_, _, advice) if advice == {libc::MADV_DONTNEED} || advice == {libc::MADV_WILLNEED}
            || advice == {libc::MADV_RANDOM} || advice == {libc::MADV_REMOVE} || advice == {libc::MADV_NORMAL}
            || advice == {libc::MADV_FREE};
        errno(libc::EPERM as u16) madvise(_, _, advice) if advice != {libc::MADV_DONTNEED}
            && advice != {libc::MADV_WILLNEED} && advice != {libc::MADV_RANDOM} && advice != {libc::MADV_REMOVE}
            && advice != {libc::MADV_NORMAL} && advice != {libc::MADV_FREE};

        allow mmap(_, _, _, flags) if flags as u32 & {!(libc::MAP_SHARED | libc::MAP_PRIVATE | libc::MAP_ANONYMOUS
            | libc::MAP_STACK | libc::MAP_NORESERVE | libc::MAP_FIXED | libc::MAP_DENYWRITE | libc::MAP_LOCKED
            | MAP_DROPPABLE)} as u32 == 0u32;

        allow mprotect(_, _, prot)
            if prot as u32 & {!(libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC | prot_arch)} as u32 == 0u32;
        allow pkey_mprotect(_, _, prot)
            if prot as u32 & {!(libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC | prot_arch)} as u32 == 0u32;

        allow prctl(option) if option == {libc::PR_GET_NAME} || option == {libc::PR_SET_NAME}
            || option == {libc::PR_GET_DUMPABLE} || option == {libc::PR_SET_DUMPABLE};
        allow prctl(option, arg) if option == PR_SET_VMA && arg as u32 == PR_SET_VMA_ANON_NAME as u32;
        trap(SIGSYS_PRCTL_FAILURE) prctl(option, arg)
            if option == PR_SET_VMA && arg as u32 != PR_SET_VMA_ANON_NAME as u32;
        errno(libc::EPERM as u16) prctl(option) if option == {libc::PR_SET_PTRACER};
        [x86_64] trap(SIGSYS_PRCTL_FAILURE) prctl(option) if option != {libc::PR_GET_NAME}
            && option != {libc::PR_SET_NAME} && option != {libc::PR_GET_DUMPABLE} && option != {libc::PR_SET_DUMPABLE}
            && option != PR_SET_VMA && option != {libc::PR_SET_PTRACER};
        [aarch64] trap(SIGSYS_PRCTL_FAILURE) prctl(option) if option != {libc::PR_GET_NAME}
            && option != {libc::PR_SET_NAME} && option != {libc::PR_GET_DUMPABLE} && option != {libc::PR_SET_DUMPABLE}
            && option != PR_SET_VMA && option != {libc::PR_SET_PTRACER}
            && option != PR_SVE_GET_VL && option != PR_SME_GET_VL;

        allow exact socketpair(domain) if domain == {libc::AF_UNIX};

        allow mincore();

        allow kill(pid) if pid == {policy_pid};
        trap(SIGSYS_KILL_FAILURE) kill(pid) if pid != {policy_pid};
        allow tgkill(tgid) if tgid == {policy_pid};
        trap(SIGSYS_KILL_FAILURE) tgkill(tgid) if tgid != {policy_pid};
        trap(SIGSYS_KILL_FAILURE) tkill();

        allow memfd_create(_, flags)
            if flags & {!(libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING | libc::MFD_NOEXEC_SEAL)} == 0u32
            || flags == {u32::MAX};

        trap(SIGSYS_FSTATAT_HANDLER) newfstatat();

        errno(libc::ENOSYS as u16) statx(_, _, _, mask) if mask == STATX_BASIC_STATS;
        errno(libc::EPERM as u16) statx(_, _, _, mask) if mask != STATX_BASIC_STATS;

        allow setitimer(which) if which == {libc::ITIMER_REAL};
        errno(libc::EPERM as u16) setitimer(which) if which != {libc::ITIMER_REAL};

        errno(libc::EPERM as u16) access();
        errno(libc::EPERM as u16) chmod();
        errno(libc::EPERM as u16) chown();
        errno(libc::EPERM as u16) creat();
        errno(libc::EPERM as u16) futimesat();
        errno(libc::EPERM as u16) lchown();
        errno(libc::EPERM as u16) link();
        errno(libc::EPERM as u16) lstat();
        errno(libc::EPERM as u16) mkdir();
        errno(libc::EPERM as u16) mknod();
        errno(libc::EPERM as u16) open();
        errno(libc::EPERM as u16) readlink();
        errno(libc::EPERM as u16) rename();
        errno(libc::EPERM as u16) rmdir();
        errno(libc::EPERM as u16) stat();
        errno(libc::EPERM as u16) symlink();
        errno(libc::EPERM as u16) unlink();
        errno(libc::EPERM as u16) uselib();
        errno(libc::EPERM as u16) ustat();
        errno(libc::EPERM as u16) utimes();
        errno(libc::EPERM as u16) execve();
        errno(libc::EPERM as u16) faccessat();
        errno(libc::EPERM as u16) faccessat2();
        errno(libc::EPERM as u16) fchmodat();
        errno(libc::EPERM as u16) fchownat();
        errno(libc::EPERM as u16) linkat();
        errno(libc::EPERM as u16) lookup_dcookie();
        errno(libc::EPERM as u16) mkdirat();
        errno(libc::EPERM as u16) mknodat();
        errno(libc::EPERM as u16) openat();
        errno(libc::EPERM as u16) readlinkat();
        errno(libc::EPERM as u16) renameat();
        errno(libc::EPERM as u16) renameat2();
        errno(libc::EPERM as u16) statfs();
        errno(libc::EPERM as u16) symlinkat();
        errno(libc::EPERM as u16) truncate();
        errno(libc::EPERM as u16) unlinkat();
        errno(libc::EPERM as u16) utime();
        errno(libc::EPERM as u16) utimensat();

        errno(libc::EPERM as u16) getcwd();
        errno(libc::EPERM as u16) chdir();
        errno(libc::EPERM as u16) fchdir();

        errno(libc::EPERM as u16) seccomp();

        errno(libc::EPERM as u16) msgctl();
        errno(libc::EPERM as u16) msgget();
        errno(libc::EPERM as u16) msgrcv();
        errno(libc::EPERM as u16) msgsnd();
        errno(libc::EPERM as u16) semctl();
        errno(libc::EPERM as u16) semget();
        errno(libc::EPERM as u16) semop();
        errno(libc::EPERM as u16) semtimedop();
        errno(libc::EPERM as u16) shmat();
        errno(libc::EPERM as u16) shmctl();
        errno(libc::EPERM as u16) shmdt();
        errno(libc::EPERM as u16) shmget();

        errno(libc::EPERM as u16) umask();

        errno(libc::EPERM as u16) fallocate();
        errno(libc::EPERM as u16) fchmod();
        errno(libc::EPERM as u16) fchown();
        errno(libc::EPERM as u16) getdents();
        errno(libc::EPERM as u16) getdents64();

        errno(libc::EPERM as u16) accept();
        errno(libc::EPERM as u16) accept4();
        errno(libc::EPERM as u16) bind();
        errno(libc::EPERM as u16) connect();
        errno(libc::EPERM as u16) socket();
        errno(libc::EPERM as u16) listen();

        errno(libc::EPERM as u16) capset();
        errno(libc::EPERM as u16) ioperm();
        errno(libc::EPERM as u16) iopl();
        errno(libc::EPERM as u16) setfsgid();
        errno(libc::EPERM as u16) setfsuid();
        errno(libc::EPERM as u16) setgid();
        errno(libc::EPERM as u16) setgroups();
        errno(libc::EPERM as u16) setregid();
        errno(libc::EPERM as u16) setresgid();
        errno(libc::EPERM as u16) setresuid();
        errno(libc::EPERM as u16) setreuid();
        errno(libc::EPERM as u16) setuid();

        allow exact getsockopt(_, level, optname) if level == {libc::SOL_SOCKET} && optname == {libc::SO_PEEK_OFF};
        allow exact setsockopt(_, level, optname) if level == {libc::SOL_SOCKET} && optname == {libc::SO_PEEK_OFF};

        allow rt_tgsigqueueinfo(tgid) if tgid == {policy_pid};
        errno(libc::EPERM as u16) rt_tgsigqueueinfo(tgid) if tgid != {policy_pid};

        allow pipe();
        allow pipe2(_, flags) if flags & {!(libc::O_CLOEXEC | libc::O_DIRECT | libc::O_NONBLOCK)} == 0;

        // `Unexpected64bitArgument` in `policy_compiler.cc`, on the arguments seacomb sees in full.
        trap(UNEXPECTED_64BIT) mmap(_, _, _, flags) if flags & {UPPER_HALF} as usize != 0usize
            && flags & {SIGN_EXTENDED} as usize != {SIGN_EXTENDED} as usize;
        trap(UNEXPECTED_64BIT) mprotect(_, _, prot) if prot & {UPPER_HALF} as usize != 0usize
            && prot & {SIGN_EXTENDED} as usize != {SIGN_EXTENDED} as usize;
        trap(UNEXPECTED_64BIT) pkey_mprotect(_, _, prot) if prot & {UPPER_HALF} as usize != 0usize
            && prot & {SIGN_EXTENDED} as usize != {SIGN_EXTENDED} as usize;
        trap(UNEXPECTED_64BIT) pkey_alloc(flags) if flags & {UPPER_HALF} as usize != 0usize
            && flags & {SIGN_EXTENDED} as usize != {SIGN_EXTENDED} as usize;
        trap(UNEXPECTED_64BIT) prctl(option, arg) if option == PR_SET_VMA && arg & {UPPER_HALF} as usize != 0usize
            && arg & {SIGN_EXTENDED} as usize != {SIGN_EXTENDED} as usize;

        // `CheckSyscallNumber` in `policy_compiler.cc` sends -1 to the x32 trap.
        [x86_64] trap(PANIC_ABI_MIXING) skip();
    }.unwrap();

    policy.install().unwrap();
    let mut args = std::env::args_os().skip(1);
    if let Some(program) = args.next() {
        panic!("{}", std::process::Command::new(program).args(args).exec());
    }
}
