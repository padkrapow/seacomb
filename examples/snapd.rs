//! snapd's filters for a strict snap,
//! [`defaultTemplate`](https://github.com/canonical/snapd/blob/2.77.1/interfaces/seccomp/template.go).

#![recursion_limit = "1024"]

#[cfg(not(target_os = "linux"))]
fn main() {}

#[cfg(target_os = "linux")]
fn main() {
    use seacomb::*;
    use std::os::unix::process::CommandExt;

    const KCMP_FILE: i32 = 0;
    const SYS_SOCKET: i32 = 1;
    const AF_QIPCRTR: i32 = 42;

    let compat = match Arch::native().unwrap() {
        Arch::X86_64 => Arch::X86,
        Arch::Aarch64 => Arch::Arm,
        _ => unimplemented!(),
    };

    let allow = policy! {
        default errno(libc::EPERM as u16) on native, {compat};

        allow access();
        allow faccessat();
        allow faccessat2();

        allow alarm();
        allow brk();

        allow breakpoint();
        allow cacheflush();
        allow get_tls();
        allow set_tls();
        allow usr26();
        allow usr32();

        allow cachestat(_, _, _, flags) if flags == 0u32;

        allow mseal(_, _, flags) if flags == 0usize;
        allow map_shadow_stack();

        allow capget();
        allow capset();

        allow chdir();
        allow fchdir();

        allow chmod();
        allow fchmod();
        allow fchmodat();
        allow fchmodat2();

        [x86, arm] allow chown(_, owner, group) if owner == 0u16 && group == 0u16
            || owner == 0u16 && group == -1 as u16 || owner == -1 as u16 && group == 0u16;
        [x86_64] allow chown(_, owner, group) if owner == 0u32 && group == 0u32
            || owner == 0u32 && group == -1 as u32 || owner == -1 as u32 && group == 0u32;
        [x86, arm] allow chown32(_, owner, group) if owner == 0u32 && group == 0u32
            || owner == 0u32 && group == -1 as u32 || owner == -1 as u32 && group == 0u32;
        [x86, arm] allow fchown(_, owner, group) if owner == 0u16 && group == 0u16
            || owner == 0u16 && group == -1 as u16 || owner == -1 as u16 && group == 0u16;
        [x86_64, aarch64] allow fchown(_, owner, group) if owner == 0u32 && group == 0u32
            || owner == 0u32 && group == -1 as u32 || owner == -1 as u32 && group == 0u32;
        [x86, arm] allow fchown32(_, owner, group) if owner == 0u32 && group == 0u32
            || owner == 0u32 && group == -1 as u32 || owner == -1 as u32 && group == 0u32;
        allow fchownat(_, _, owner, group) if owner == 0u32 && group == 0u32
            || owner == 0u32 && group == -1 as u32 || owner == -1 as u32 && group == 0u32;
        [x86, arm] allow lchown(_, owner, group) if owner == 0u16 && group == 0u16
            || owner == 0u16 && group == -1 as u16 || owner == -1 as u16 && group == 0u16;
        [x86_64] allow lchown(_, owner, group) if owner == 0u32 && group == 0u32
            || owner == 0u32 && group == -1 as u32 || owner == -1 as u32 && group == 0u32;
        [x86, arm] allow lchown32(_, owner, group) if owner == 0u32 && group == 0u32
            || owner == 0u32 && group == -1 as u32 || owner == -1 as u32 && group == 0u32;

        allow clock_getres();
        allow clock_getres_time64();
        allow clock_gettime();
        allow clock_gettime64();
        allow clock_nanosleep();
        allow clock_nanosleep_time64();
        allow clone();
        allow clone3();
        allow close();
        allow close_range();

        allow connect();

        allow copy_file_range(_, _, _, _, _, flags) if flags == 0u32;

        allow chroot();

        allow creat();

        allow dup();
        allow dup2();
        allow dup3();
        allow epoll_create();
        allow epoll_create1();
        allow epoll_ctl();
        allow epoll_ctl_old();
        allow epoll_pwait();
        allow epoll_pwait2();
        allow epoll_wait();
        allow epoll_wait_old();
        allow eventfd();
        allow eventfd2();
        allow execve();
        allow execveat();
        allow exit();
        allow exit_group();
        allow fallocate();

        allow fcntl();
        allow fcntl64();
        allow flock();
        allow fork();
        allow ftime();
        allow futex();
        allow futex_requeue();
        allow futex_time64();
        allow futex_wait();
        allow futex_waitv();
        allow futex_wake();
        allow get_mempolicy();
        allow get_robust_list();
        allow get_thread_area();
        allow getcpu();
        allow getcwd();
        allow getdents();
        allow getdents64();
        allow getegid();
        allow getegid32();
        allow geteuid();
        allow geteuid32();
        allow getgid();
        allow getgid32();
        allow getgroups();
        allow getgroups32();
        allow getitimer();
        allow getpgid();
        allow getpgrp();
        allow getpid();
        allow getppid();
        allow pidfd_open();
        allow getpriority();
        allow getrandom();
        allow getresgid();
        allow getresgid32();
        allow getresuid();
        allow getresuid32();

        allow getrlimit();
        allow ugetrlimit();

        allow getrusage();
        allow getsid();
        allow gettid();
        allow gettimeofday();
        allow getuid();
        allow getuid32();

        allow getxattr();
        allow fgetxattr();
        allow lgetxattr();
        allow getxattrat();

        allow inotify_add_watch();
        allow inotify_init();
        allow inotify_init1();
        allow inotify_rm_watch();

        allow ioctl();

        allow io_cancel();
        allow io_destroy();
        allow io_getevents();
        allow io_pgetevents();
        allow io_pgetevents_time64();
        allow io_setup();
        allow io_submit();
        allow ioprio_get();

        allow ipc();
        allow kill();
        allow kcmp(_, _, kind) if kind == KCMP_FILE;
        allow link();
        allow linkat();

        allow listxattr();
        allow llistxattr();
        allow flistxattr();
        allow listxattrat();

        allow lseek();
        allow _llseek();
        allow lstat();
        allow lstat64();

        allow madvise();
        allow fadvise64();
        allow fadvise64_64();
        allow arm_fadvise64_64();

        allow mbind();
        allow membarrier();
        allow memfd_create();
        allow memfd_secret();
        allow mincore();
        allow mkdir();
        allow mkdirat();
        allow mlock();
        allow mlock2();
        allow mlockall();
        allow mmap();
        allow mmap2();

        [x86, x86_64, arm] allow mknod(_, mode) if mode & {libc::S_IFREG} as u16 == {libc::S_IFREG} as u16
            || mode & {libc::S_IFIFO} as u16 == {libc::S_IFIFO} as u16
            || mode & {libc::S_IFSOCK} as u16 == {libc::S_IFSOCK} as u16;
        allow mknodat(_, _, mode) if mode & {libc::S_IFREG} as u16 == {libc::S_IFREG} as u16
            || mode & {libc::S_IFIFO} as u16 == {libc::S_IFIFO} as u16
            || mode & {libc::S_IFSOCK} as u16 == {libc::S_IFSOCK} as u16;

        allow modify_ldt();
        allow mprotect();

        allow mremap();
        allow msgctl();
        allow msgget();
        allow msgrcv();
        allow msgsnd();
        allow msync();
        allow munlock();
        allow munlockall();
        allow munmap();

        allow nanosleep();

        [x86, arm] allow nice(increment) if increment as u32 <= 19u32;
        allow setpriority(which, who, prio)
            if which == {libc::PRIO_PROCESS} as i32 && who == 0 && prio as u32 <= 19u32;

        allow open();

        allow openat();

        allow pause();
        allow personality();
        allow pipe();
        allow pipe2();
        allow poll();
        allow ppoll();
        allow ppoll_time64();

        allow prctl();
        allow arch_prctl();

        allow read();
        allow pread64();
        allow preadv();
        allow readv();

        allow readahead();
        allow readdir();
        allow readlink();
        allow readlinkat();

        allow recv();
        allow recvfrom();
        allow recvmsg();
        allow recvmmsg();
        allow recvmmsg_time64();

        allow remap_file_pages();

        allow removexattr();
        allow fremovexattr();
        allow lremovexattr();
        allow removexattrat();

        allow rename();
        allow renameat();
        allow renameat2();

        allow restart_syscall();

        allow rmdir();

        allow rseq();
        allow rseq_slice_yield();

        allow rt_sigaction();
        allow rt_sigpending();
        allow rt_sigprocmask();
        allow rt_sigqueueinfo();
        allow rt_sigreturn();
        allow rt_sigsuspend();
        allow rt_sigtimedwait();
        allow rt_sigtimedwait_time64();
        allow rt_tgsigqueueinfo();
        allow sched_getaffinity();
        allow sched_getattr();
        allow sched_getparam();
        allow sched_get_priority_max();
        allow sched_get_priority_min();
        allow sched_getscheduler();
        allow sched_rr_get_interval();
        allow sched_rr_get_interval_time64();
        allow sched_setaffinity(pid) if pid == 0;
        allow sched_setparam(pid) if pid == 0;

        allow sched_setscheduler();

        allow sched_yield();

        allow seccomp();

        allow landlock_create_ruleset();
        allow landlock_add_rule();
        allow landlock_restrict_self();

        allow select();
        allow _newselect();
        allow pselect6();
        allow pselect6_time64();

        allow semctl();
        allow semget();
        allow semop();
        allow semtimedop();
        allow semtimedop_time64();

        allow send();
        allow sendto();
        allow sendmsg();
        allow sendmmsg();

        allow sendfile();
        allow sendfile64();

        allow setpgid();

        allow set_thread_area();
        allow setitimer();

        allow setrlimit();
        allow prlimit64();

        allow set_mempolicy();
        allow set_robust_list();
        allow setsid();
        allow set_tid_address();

        allow setxattr();
        allow fsetxattr();
        allow lsetxattr();
        allow setxattrat();

        allow shmat();
        allow shmctl();
        allow shmdt();
        allow shmget();
        allow shutdown();
        allow signal();
        allow sigaction();
        allow signalfd();
        allow signalfd4();
        allow sigaltstack();
        allow sigpending();
        allow sigprocmask();
        allow sigreturn();
        allow sigsuspend();

        allow exact socket(domain) if domain == {libc::AF_UNIX} || domain == {libc::AF_LOCAL}
            || domain == {libc::AF_INET} || domain == {libc::AF_INET6} || domain == {libc::AF_IPX}
            || domain == {libc::AF_XDP} || domain == {libc::AF_X25} || domain == {libc::AF_AX25}
            || domain == {libc::AF_ATMPVC} || domain == {libc::AF_APPLETALK} || domain == {libc::AF_PACKET}
            || domain == {libc::AF_ALG} || domain == {libc::AF_CAN} || domain == {libc::AF_BRIDGE}
            || domain == {libc::AF_NETROM} || domain == {libc::AF_ROSE} || domain == {libc::AF_NETBEUI}
            || domain == {libc::AF_SECURITY} || domain == {libc::AF_KEY} || domain == {libc::AF_ASH}
            || domain == {libc::AF_ECONET} || domain == {libc::AF_SNA} || domain == {libc::AF_IRDA}
            || domain == {libc::AF_PPPOX} || domain == {libc::AF_WANPIPE} || domain == {libc::AF_BLUETOOTH}
            || domain == {libc::AF_RDS} || domain == {libc::AF_LLC} || domain == {libc::AF_TIPC}
            || domain == {libc::AF_IUCV} || domain == {libc::AF_RXRPC} || domain == {libc::AF_ISDN}
            || domain == {libc::AF_PHONET} || domain == {libc::AF_IEEE802154} || domain == {libc::AF_CAIF}
            || domain == {libc::AF_NFC} || domain == {libc::AF_VSOCK} || domain == {libc::AF_MPLS}
            || domain == {libc::AF_IB} || domain == AF_QIPCRTR;
        [x86] allow socketcall(call) if call == SYS_SOCKET;

        allow getsockopt();
        allow setsockopt();
        allow getsockname();
        allow getpeername();

        allow socketpair();

        allow splice();

        allow stat();
        allow stat64();
        allow fstat();
        allow fstat64();
        allow fstatat64();
        allow newfstatat();
        allow oldfstat();
        allow oldlstat();
        allow oldstat();
        allow statx();

        allow statfs();
        allow statfs64();
        allow fstatfs();
        allow fstatfs64();
        allow ustat();

        allow symlink();
        allow symlinkat();

        allow sync();
        allow sync_file_range();
        allow arm_sync_file_range();
        allow fdatasync();
        allow fsync();
        allow syncfs();
        allow sysinfo();
        allow syslog();
        allow tee();
        allow tgkill();
        allow time();
        allow timer_create();
        allow timer_delete();
        allow timer_getoverrun();
        allow timer_gettime();
        allow timer_gettime64();
        allow timer_settime();
        allow timer_settime64();
        allow timerfd_create();
        allow timerfd_gettime();
        allow timerfd_gettime64();
        allow timerfd_settime();
        allow timerfd_settime64();
        allow times();
        allow tkill();

        allow truncate();
        allow truncate64();
        allow ftruncate();
        allow ftruncate64();

        allow umask();

        allow uname();
        allow olduname();
        allow oldolduname();

        allow unlink();
        allow unlinkat();

        allow utime();
        allow utimensat();
        allow utimensat_time64();
        allow utimes();
        allow futimesat();

        allow vfork();
        allow vmsplice();
        allow wait4();
        allow waitpid();
        allow waitid();

        allow write();
        allow writev();
        allow pwrite64();
        allow pwritev();
        allow pwritev2();

        allow setgid();
        allow setgid32();
        allow setregid();
        allow setregid32();
        allow setresgid();
        allow setresgid32();
        allow setresuid();
        allow setresuid32();
        allow setreuid();
        allow setreuid32();
        allow setuid();
        allow setuid32();
    }.unwrap();

    let deny = policy! {
        default allow on native, {compat};

        [x86, x86_64, arm] errno(libc::EACCES as u16) chmod(_, mode)
            if mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;
        errno(libc::EACCES as u16) fchmod(_, mode) if mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;
        errno(libc::EACCES as u16) fchmodat(_, _, mode) if mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;
        errno(libc::EACCES as u16) fchmodat2(_, _, mode) if mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;

        [x86, x86_64, arm] errno(libc::EACCES as u16) creat(_, mode)
            if mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;

        errno(libc::EACCES as u16) ioctl(_, request)
            if request == {libc::TIOCSTI} as u32 || request == {libc::TIOCLINUX} as u32;

        [x86, x86_64, arm] errno(libc::EACCES as u16) mknod(_, mode)
            if mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;
        errno(libc::EACCES as u16) mknodat(_, _, mode) if mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;

        errno(libc::EACCES as u16) openat2();

        [x86, x86_64, arm] errno(libc::EACCES as u16) open(_, flags, mode)
            if (flags & {libc::O_CREAT} == {libc::O_CREAT} || flags & {libc::O_TMPFILE} == {libc::O_TMPFILE})
            && mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;
        errno(libc::EACCES as u16) openat(_, _, flags, mode)
            if (flags & {libc::O_CREAT} == {libc::O_CREAT} || flags & {libc::O_TMPFILE} == {libc::O_TMPFILE})
            && mode & {libc::S_ISUID | libc::S_ISGID} as u16 != 0u16;

        errno(libc::EACCES as u16) pipe2(_, flags) if flags & {libc::O_EXCL} == {libc::O_EXCL};
    }.unwrap();

    deny.install().unwrap();
    allow.install().unwrap();
    let mut args = std::env::args_os().skip(1);
    if let Some(program) = args.next() {
        panic!("{}", std::process::Command::new(program).args(args).exec());
    }
}
