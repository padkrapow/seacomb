//! Firecracker's filter for the VMM thread in
//! [`x86_64-unknown-linux-musl.json`](https://github.com/firecracker-microvm/firecracker/blob/v1.17.0/resources/seccomp/x86_64-unknown-linux-musl.json)
//! and [`aarch64-unknown-linux-musl.json`](https://github.com/firecracker-microvm/firecracker/blob/v1.17.0/resources/seccomp/aarch64-unknown-linux-musl.json).

#![recursion_limit = "512"]

#[cfg(not(target_os = "linux"))]
fn main() {}

#[cfg(target_os = "linux")]
fn main() {
    use seacomb::*;
    use std::os::unix::process::CommandExt;

    const VCPU_RTSIG: i32 = 35;
    const BLKDISCARD: u32 = 0x1277;
    const KVM_GET_DIRTY_LOG: u32 = 0x4010_ae42;
    const KVM_GET_IRQCHIP: u32 = 0xc208_ae62;
    const KVM_GET_CLOCK: u32 = 0x8030_ae7c;
    const KVM_GET_PIT2: u32 = 0x8070_ae9f;
    const KVM_SET_USER_MEMORY_REGION: u32 = 0x4020_ae46;
    const KVM_IOEVENTFD: u32 = 0x4040_ae79;
    const KVM_IRQFD: u32 = 0x4020_ae76;
    const KVM_SET_DEVICE_ATTR: u32 = 0x4018_aee1;
    const KVM_GET_DEVICE_ATTR: u32 = 0x4018_aee2;

    let policy = policy! {
        default trap(0) on native;

        [x86_64] allow stat();
        [aarch64] allow newfstatat();
        allow epoll_ctl();
        allow epoll_pwait();
        allow exit();
        allow exit_group();
        [x86_64] allow open();
        [aarch64] allow openat();
        allow read();
        allow write();
        allow mincore();
        allow writev();
        allow readv();
        allow fsync();
        allow fallocate(_, mode) if mode == {libc::FALLOC_FL_KEEP_SIZE | libc::FALLOC_FL_PUNCH_HOLE};
        allow close();
        allow eventfd2();
        allow io_uring_enter();
        allow io_uring_setup();
        allow io_uring_register();
        allow brk();
        allow gettid();
        allow clock_gettime();
        allow connect();
        allow fstat();
        allow ftruncate();
        allow lseek();
        allow mremap();
        allow munmap();
        allow recvfrom();
        allow rt_sigprocmask();
        allow rt_sigreturn();
        allow sigaltstack();
        allow getrandom();
        allow accept4(_, _, _, flags) if flags == {libc::SOCK_CLOEXEC};
        allow fcntl(_, cmd, arg) if cmd == {libc::F_SETFD} as u32 && arg as u32 == {libc::FD_CLOEXEC} as u32;

        allow futex(_, op) if op == {libc::FUTEX_WAIT};
        allow futex(_, op) if op == {libc::FUTEX_WAKE};
        allow futex(_, op) if op == {libc::FUTEX_WAIT | libc::FUTEX_PRIVATE_FLAG};
        allow futex(_, op) if op == {libc::FUTEX_WAIT_BITSET | libc::FUTEX_PRIVATE_FLAG};
        allow futex(_, op) if op == {libc::FUTEX_WAKE | libc::FUTEX_PRIVATE_FLAG};

        allow madvise();
        allow msync(_, _, flags) if flags == {libc::MS_SYNC};

        allow mmap(_, _, prot, flags) if flags as u32
            == {libc::MAP_NORESERVE | libc::MAP_ANONYMOUS | libc::MAP_FIXED | libc::MAP_PRIVATE} as u32
            && prot & {libc::PROT_EXEC} as usize == 0usize;
        allow mmap(_, _, prot, flags)
            if flags as u32 == {libc::MAP_SHARED} as u32 && prot & {libc::PROT_EXEC} as usize == 0usize;
        allow mmap(_, _, prot, flags) if flags as u32 == {libc::MAP_ANONYMOUS | libc::MAP_PRIVATE} as u32
            && prot & {libc::PROT_EXEC} as usize == 0usize;
        allow mmap(_, _, prot, flags) if flags as u32 == {libc::MAP_POPULATE | libc::MAP_SHARED} as u32
            && prot & {libc::PROT_EXEC} as usize == 0usize;
        allow mmap(_, _, prot, flags) if flags as u32 == {libc::MAP_NORESERVE | libc::MAP_SHARED} as u32
            && prot & {libc::PROT_EXEC} as usize == 0usize;
        allow mmap(_, _, prot, flags)
            if flags as u32 == {libc::MAP_NORESERVE | libc::MAP_ANONYMOUS | libc::MAP_PRIVATE} as u32
            && prot & {libc::PROT_EXEC} as usize == 0usize;
        allow mmap(_, _, prot, flags)
            if flags as u32 == {libc::MAP_NORESERVE | libc::MAP_FIXED | libc::MAP_SHARED} as u32
            && prot & {libc::PROT_EXEC} as usize == 0usize;
        allow mmap(_, _, prot, flags) if flags as u32 == {libc::MAP_FIXED | libc::MAP_SHARED} as u32
            && prot as u32 == {libc::PROT_READ | libc::PROT_WRITE} as u32;

        allow memfd_create(_, flags) if flags == {libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING};
        allow fcntl(_, cmd) if cmd == {libc::F_ADD_SEALS} as u32;
        allow rt_sigaction(sig) if sig == {libc::SIGABRT};
        allow socket(domain, ty, protocol)
            if domain == {libc::AF_UNIX} && ty == {libc::SOCK_STREAM | libc::SOCK_CLOEXEC} && protocol == 0;
        allow sendto();

        allow tkill(_, sig) if sig == {libc::SIGABRT};
        allow tkill(_, sig) if sig == VCPU_RTSIG;

        allow timerfd_create(clockid, flags)
            if clockid == {libc::CLOCK_MONOTONIC} && flags == {libc::TFD_CLOEXEC | libc::TFD_NONBLOCK};
        allow timerfd_settime(_, flags) if flags == 0;

        allow ioctl(_, request) if request == {libc::FIONBIO} as u32;
        allow ioctl(_, request) if request == {libc::TIOCGWINSZ} as u32;
        allow ioctl(_, request) if request == {libc::TCGETS} as u32;
        allow ioctl(_, request) if request == {libc::TCSETS} as u32;
        allow ioctl(_, request) if request == BLKDISCARD;
        allow ioctl(_, request) if request == KVM_GET_DIRTY_LOG;
        [x86_64] allow ioctl(_, request) if request == KVM_GET_IRQCHIP;
        [x86_64] allow ioctl(_, request) if request == KVM_GET_CLOCK;
        [x86_64] allow ioctl(_, request) if request == KVM_GET_PIT2;
        [aarch64] allow ioctl(_, request) if request == KVM_SET_DEVICE_ATTR;
        [aarch64] allow ioctl(_, request) if request == KVM_GET_DEVICE_ATTR;
        allow ioctl(_, request) if request == KVM_SET_USER_MEMORY_REGION;
        allow ioctl(_, request) if request == KVM_IOEVENTFD;
        allow ioctl(_, request) if request == KVM_IRQFD;
        allow ioctl(_, request) if request == {libc::TUNSETIFF} as u32;
        allow ioctl(_, request) if request == {libc::TUNSETOFFLOAD} as u32;
        allow ioctl(_, request) if request == {libc::TUNSETVNETHDRSZ} as u32;
        allow ioctl(_, request) if request == {libc::BLKSSZGET} as u32;
        allow ioctl(_, request) if request == {libc::BLKPBSZGET} as u32;
        allow ioctl(_, request) if request == {libc::BLKIOMIN} as u32;
        allow ioctl(_, request) if request == {libc::BLKIOOPT} as u32;

        allow sched_yield();
        allow sendmsg();
        allow recvmsg();
        allow restart_syscall();
        allow mprotect(_, _, prot) if prot & {libc::PROT_EXEC} as usize == 0usize;
    }.unwrap();

    policy.install().unwrap();
    let mut args = std::env::args_os().skip(1);
    if let Some(program) = args.next() {
        panic!("{}", std::process::Command::new(program).args(args).exec());
    }
}
