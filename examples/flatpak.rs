//! Flatpak's sandbox filter,
//! [`setup_seccomp`](https://github.com/flatpak/flatpak/blob/1.18.4/common/flatpak-run.c#L1998).

#![recursion_limit = "256"]

#[cfg(not(target_os = "linux"))]
fn main() {}

#[cfg(target_os = "linux")]
fn main() {
    use seacomb::*;
    use std::os::unix::process::CommandExt;

    const PER_LINUX: u32 = 0x0000;

    let policy = policy! {
        default allow on native;

        errno(libc::EPERM as u16) syslog();
        errno(libc::EPERM as u16) uselib();
        errno(libc::EPERM as u16) acct();
        errno(libc::EPERM as u16) quotactl();

        errno(libc::EPERM as u16) add_key();
        errno(libc::EPERM as u16) keyctl();
        errno(libc::EPERM as u16) request_key();

        errno(libc::EPERM as u16) move_pages();
        errno(libc::EPERM as u16) mbind();
        errno(libc::EPERM as u16) get_mempolicy();
        errno(libc::EPERM as u16) set_mempolicy();
        errno(libc::EPERM as u16) migrate_pages();

        errno(libc::EPERM as u16) unshare();
        errno(libc::EPERM as u16) setns();
        errno(libc::EPERM as u16) mount();
        errno(libc::EPERM as u16) umount();
        errno(libc::EPERM as u16) umount2();
        errno(libc::EPERM as u16) pivot_root();
        errno(libc::EPERM as u16) chroot();
        errno(libc::EPERM as u16) clone(flags)
            if flags & {libc::CLONE_NEWUSER} as usize == {libc::CLONE_NEWUSER} as usize;

        errno(libc::EPERM as u16) ioctl(_, request)
            if request == {libc::TIOCSTI} as u32 || request == {libc::TIOCLINUX} as u32;

        errno(libc::ENOSYS as u16) clone3();

        errno(libc::ENOSYS as u16) open_tree();
        errno(libc::ENOSYS as u16) move_mount();
        errno(libc::ENOSYS as u16) fsopen();
        errno(libc::ENOSYS as u16) fsconfig();
        errno(libc::ENOSYS as u16) fsmount();
        errno(libc::ENOSYS as u16) fspick();
        errno(libc::ENOSYS as u16) mount_setattr();

        errno(libc::EPERM as u16) modify_ldt();

        errno(libc::EPERM as u16) perf_event_open();
        errno(libc::EPERM as u16) personality(persona) if persona != PER_LINUX;
        errno(libc::EPERM as u16) ptrace();

        errno(libc::EAFNOSUPPORT as u16) exact socket(domain) if
            domain != {libc::AF_UNSPEC} && domain != {libc::AF_LOCAL} && domain != {libc::AF_INET} &&
            domain != {libc::AF_INET6} && domain != {libc::AF_NETLINK};
    }.unwrap();

    policy.install().unwrap();
    let mut args = std::env::args_os().skip(1);
    if let Some(program) = args.next() {
        panic!("{}", std::process::Command::new(program).args(args).exec());
    }
}
