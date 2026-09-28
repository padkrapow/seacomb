//! Tests of argument conditions and syscall signatures.

use super::*;

/// Equality on an `int` argument compares it as a 32-bit signed value.
#[test]
fn i32_eq() {
    let filter = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 == -1));
    unsafe {
        filter.install_and_check(libc::SYS_getpriority, [-1i64 as libc::c_ulong, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_getpriority, [-2i64 as libc::c_ulong, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_getpriority, [0, 0, 0, 0, 0, 0], Expect::Ok);
    }
}

/// An `int` argument ignores the register bits above its low word, as the kernel does.
#[cfg(target_pointer_width = "64")]
#[test]
fn i32_high_word() {
    let minus_one = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 == -1));
    let negative = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 < 0));
    let not_minus_one = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 != -1));
    unsafe {
        minus_one.install_and_check(libc::SYS_getpriority, [0xffff_ffff, 0, 0, 0, 0, 0], Expect::Denied);
        minus_one.install_and_check(libc::SYS_getpriority, [0x1_ffff_ffff, 0, 0, 0, 0, 0], Expect::Denied);
        minus_one.install_and_check(libc::SYS_getpriority, [0xffff_fffe_ffff_ffff, 0, 0, 0, 0, 0], Expect::Denied);
        minus_one.install_and_check(libc::SYS_getpriority, [0xffff_ffff_0000_0000, 0, 0, 0, 0, 0], Expect::Ok);
        negative.install_and_check(libc::SYS_getpriority, [0x8000_0000, 0, 0, 0, 0, 0], Expect::Denied);
        negative.install_and_check(libc::SYS_getpriority, [0xffff_ffff_0000_0001, 0, 0, 0, 0, 0], Expect::Ok);
        negative.install_and_check(libc::SYS_getpriority, [0x8000_0000_7fff_ffff, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        not_minus_one.install_and_check(libc::SYS_getpriority, [0xffff_ffff, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        not_minus_one.install_and_check(libc::SYS_getpriority, [0x1_0000_0000, 0, 0, 0, 0, 0], Expect::Denied);
    }
}

/// Ordering on an `int` argument puts negative values below zero.
#[test]
fn i32_order() {
    let min = i32::MIN as i64;
    let max = i32::MAX as i64;
    for (cond, expect) in [
        (cond!(@0 < 0), [Expect::Denied, Expect::Denied, Expect::Ok, Expect::Errno(libc::EINVAL)]),
        (cond!(@0 <= -2), [Expect::Denied, Expect::Errno(libc::EINVAL), Expect::Ok, Expect::Errno(libc::EINVAL)]),
        (cond!(@0 > -1), [Expect::Errno(libc::EINVAL), Expect::Errno(libc::EINVAL), Expect::Denied, Expect::Denied]),
        (cond!(@0 >= -1), [Expect::Errno(libc::EINVAL), Expect::Denied, Expect::Denied, Expect::Denied]),
        (cond!(@0 >= {min as i32}), [Expect::Denied; 4]),
        (cond!(@0 <= {max as i32}), [Expect::Denied; 4]),
        (cond!(@0 < {min as i32}), [Expect::Errno(libc::EINVAL), Expect::Errno(libc::EINVAL), Expect::Ok, Expect::Errno(libc::EINVAL)]),
        (cond!(@0 > {max as i32}), [Expect::Errno(libc::EINVAL), Expect::Errno(libc::EINVAL), Expect::Ok, Expect::Errno(libc::EINVAL)]),
    ] {
        let filter = Filter::new_native_deny(Syscall::Getpriority, cond);
        for (which, expect) in [i32::MIN as libc::c_long, -1, 0, i32::MAX as libc::c_long].into_iter().zip(expect) {
            unsafe { filter.install_and_check(libc::SYS_getpriority, [which as libc::c_ulong, 0, 0, 0, 0, 0], expect) };
        }
    }
}

/// Two tests on one argument bound it from both sides.
#[test]
fn i32_range() {
    let filter = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 >= 0 && @0 <= 1));
    let empty = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 > 0 && @0 < 1));
    unsafe {
        filter.install_and_check(libc::SYS_getpriority, [-1i64 as libc::c_ulong, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        filter.install_and_check(libc::SYS_getpriority, [0, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_getpriority, [1, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_getpriority, [3, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        empty.install_and_check(libc::SYS_getpriority, [0, 0, 0, 0, 0, 0], Expect::Ok);
        empty.install_and_check(libc::SYS_getpriority, [1, 0, 0, 0, 0, 0], Expect::Ok);
    }
}

/// Masked equality on an `int` argument sees its 32-bit pattern.
#[test]
fn i32_masked() {
    let sign = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 & -0x8000_0000 == -0x8000_0000));
    let all = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 & -1 == -1));
    unsafe {
        sign.install_and_check(libc::SYS_getpriority, [-1i64 as libc::c_ulong, 0, 0, 0, 0, 0], Expect::Denied);
        sign.install_and_check(libc::SYS_getpriority, [i32::MIN as libc::c_ulong, 0, 0, 0, 0, 0], Expect::Denied);
        sign.install_and_check(libc::SYS_getpriority, [0x7fff_ffff, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        all.install_and_check(libc::SYS_getpriority, [-1i64 as libc::c_ulong, 0, 0, 0, 0, 0], Expect::Denied);
        all.install_and_check(libc::SYS_getpriority, [-2i64 as libc::c_ulong, 0, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
    }
}

/// Ordering on an `unsigned int` argument puts its top bit above every other value.
#[test]
fn u32_order() {
    let filter = Filter::new_native_deny(Syscall::Dup, cond!(@0 > 0x7fff_ffffu32));
    let max = Filter::new_native_deny(Syscall::Dup, cond!(@0 >= 0xffff_ffffu32));
    unsafe {
        filter.install_and_check(libc::SYS_dup, [0x7fff_ffff, 0, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_dup, [0x8000_0000, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_dup, [0xffff_ffff, 0, 0, 0, 0, 0], Expect::Denied);
        max.install_and_check(libc::SYS_dup, [0xffff_fffe, 0, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        max.install_and_check(libc::SYS_dup, [0xffff_ffff, 0, 0, 0, 0, 0], Expect::Denied);
    }
}

/// An `unsigned int` argument ignores the register bits above its low word.
#[cfg(target_pointer_width = "64")]
#[test]
fn u32_high_word() {
    let filter = Filter::new_native_deny(Syscall::Dup, cond!(@0 > 0x7fff_ffffu32));
    let max = Filter::new_native_deny(Syscall::Dup, cond!(@0 == 0xffff_ffffu32));
    unsafe {
        filter.install_and_check(libc::SYS_dup, [0x1_7fff_ffff, 0, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_dup, [0xffff_ffff_7fff_ffff, 0, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_dup, [0x1_8000_0000, 0, 0, 0, 0, 0], Expect::Denied);
        max.install_and_check(libc::SYS_dup, [libc::c_ulong::MAX, 0, 0, 0, 0, 0], Expect::Denied);
        max.install_and_check(libc::SYS_dup, [0x1234_5678_ffff_ffff, 0, 0, 0, 0, 0], Expect::Denied);
    }
}

/// Ordering and masking on a 16-bit argument ignore the register bits above it.
#[test]
fn u16_order() {
    let fd = libc::c_ulong::MAX;
    let above = Filter::new_native_deny(Syscall::Fchmod, cond!(@1 > 0o7777u16));
    let special = Filter::new_native_deny(Syscall::Fchmod, cond!(@1 & 0o7000u16 == 0u16));
    unsafe {
        above.install_and_check(libc::SYS_fchmod, [fd, 0o7777, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        above.install_and_check(libc::SYS_fchmod, [fd, 0x1_0000, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        above.install_and_check(libc::SYS_fchmod, [fd, 0xffff_0fff, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        above.install_and_check(libc::SYS_fchmod, [fd, 0xffff, 0, 0, 0, 0], Expect::Denied);
        special.install_and_check(libc::SYS_fchmod, [fd, 0o755, 0, 0, 0, 0], Expect::Denied);
        special.install_and_check(libc::SYS_fchmod, [fd, 0x7_0000 | 0o755, 0, 0, 0, 0], Expect::Denied);
        special.install_and_check(libc::SYS_fchmod, [fd, 0o4755, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// Ordering on a `long` argument is signed at the native word width.
#[test]
fn iword_order() {
    let fd = libc::c_ulong::MAX;
    let sign: libc::c_ulong = 1 << (libc::c_ulong::BITS - 1);
    let from_minus_one = Filter::new_native_deny(Syscall::Lseek, cond!(@1 >= -1isize));
    let top_bit = Filter::new_native_deny(Syscall::Lseek, cond!(@1 & {sign as isize} == {sign as isize}));
    for (offset, expect) in [
        (sign, Expect::Errno(libc::EBADF)),
        (-2i64 as libc::c_ulong, Expect::Errno(libc::EBADF)),
        (-1i64 as libc::c_ulong, Expect::Denied),
        (0, Expect::Denied),
        (sign - 1, Expect::Denied),
    ] {
        unsafe { from_minus_one.install_and_check(libc::SYS_lseek, [fd, offset, 0, 0, 0, 0], expect) };
    }
    for (offset, expect) in [
        (sign, Expect::Denied),
        (-1i64 as libc::c_ulong, Expect::Denied),
        (0, Expect::Errno(libc::EBADF)),
        (sign - 1, Expect::Errno(libc::EBADF)),
    ] {
        unsafe { top_bit.install_and_check(libc::SYS_lseek, [fd, offset, 0, 0, 0, 0], expect) };
    }
}

/// On a 64-bit architecture, a `long` argument whose low word looks negative is still positive.
#[cfg(target_pointer_width = "64")]
#[test]
fn iword_64() {
    let fd = libc::c_ulong::MAX;
    let filter = Filter::new_native_deny(Syscall::Lseek, cond!(@1 < 0isize));
    let low = Filter::new_native_deny(Syscall::Lseek, cond!(@1 == 0xffff_ffffisize));
    unsafe {
        filter.install_and_check(libc::SYS_lseek, [fd, 0x8000_0000, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_lseek, [fd, 0xffff_ffff, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_lseek, [fd, 0xffff_ffff_0000_0000, 0, 0, 0, 0], Expect::Denied);
        low.install_and_check(libc::SYS_lseek, [fd, 0xffff_ffff, 0, 0, 0, 0], Expect::Denied);
        low.install_and_check(libc::SYS_lseek, [fd, libc::c_ulong::MAX, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// Ordering on an `unsigned long` argument reaches its largest value.
#[test]
fn uword_bounds() {
    let max = u64::MAX >> (u64::BITS - libc::c_ulong::BITS);
    let at_max = Filter::new_native_deny(Syscall::Mprotect, cond!(@1 >= {max as usize}));
    let below_max = Filter::new_native_deny(Syscall::Mprotect, cond!(@1 < {max as usize}));
    let below = max - 1;
    let exact = Filter::new_native_deny(Syscall::Mprotect, cond!(@1 & {max as usize} == {below as usize}));
    // An unaligned start makes mprotect fail with EINVAL whatever the length.
    unsafe {
        at_max.install_and_check(libc::SYS_mprotect, [1, libc::c_ulong::MAX, 0, 0, 0, 0], Expect::Denied);
        at_max.install_and_check(libc::SYS_mprotect, [1, libc::c_ulong::MAX - 1, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        below_max.install_and_check(libc::SYS_mprotect, [1, libc::c_ulong::MAX, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
        below_max.install_and_check(libc::SYS_mprotect, [1, 0, 0, 0, 0, 0], Expect::Denied);
        exact.install_and_check(libc::SYS_mprotect, [1, libc::c_ulong::MAX - 1, 0, 0, 0, 0], Expect::Denied);
        exact.install_and_check(libc::SYS_mprotect, [1, libc::c_ulong::MAX, 0, 0, 0, 0], Expect::Errno(libc::EINVAL));
    }
}

/// A pointer argument takes equality and inequality, and masked equality once cast to a word.
#[test]
fn ptr() {
    let top = libc::c_ulong::MAX & !0xfff;
    let null = Filter::new_native_deny(Syscall::Uname, cond!(@0 == 0 as ptr));
    let non_null = Filter::new_native_deny(Syscall::Uname, cond!(@0 != 0 as ptr));
    let aligned = Filter::new_native_deny(Syscall::Uname, cond!(@0 as usize & 0xfffusize == 0usize));
    // Neither 0, 1, nor the top page of the address space is mapped, so uname only faults.
    unsafe {
        null.install_and_check(libc::SYS_uname, [0, 0, 0, 0, 0, 0], Expect::Denied);
        null.install_and_check(libc::SYS_uname, [1, 0, 0, 0, 0, 0], Expect::Errno(libc::EFAULT));
        non_null.install_and_check(libc::SYS_uname, [0, 0, 0, 0, 0, 0], Expect::Errno(libc::EFAULT));
        non_null.install_and_check(libc::SYS_uname, [top, 0, 0, 0, 0, 0], Expect::Denied);
        aligned.install_and_check(libc::SYS_uname, [top, 0, 0, 0, 0, 0], Expect::Denied);
        aligned.install_and_check(libc::SYS_uname, [top | 1, 0, 0, 0, 0, 0], Expect::Errno(libc::EFAULT));
    }
}

/// On a 64-bit architecture, pointer equality looks at both words of the address.
#[cfg(target_pointer_width = "64")]
#[test]
fn ptr_64() {
    let filter = Filter::new_native_deny(Syscall::Uname, cond!(@0 == 0xffff_fffe_0000_0000u64 as ptr));
    unsafe {
        filter.install_and_check(libc::SYS_uname, [0xffff_fffe_0000_0000, 0, 0, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_uname, [0xffff_ffff_0000_0000, 0, 0, 0, 0, 0], Expect::Errno(libc::EFAULT));
    }
}

/// A rule's conditions only narrow that rule, and a higher-precedence action still wins where they hold.
#[test]
fn conds_with_other_rules() {
    let fd = libc::c_ulong::MAX;
    for first in [false, true] {
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        if first {
            filter.add_rule(Expect::DENY, Syscall::Lseek, cond!(@1 == 7isize)).unwrap();
        }
        filter.add_rule(Action::Log, Syscall::Lseek, Cond::True).unwrap();
        if !first {
            filter.add_rule(Expect::DENY, Syscall::Lseek, cond!(@1 == 7isize)).unwrap();
        }
        unsafe {
            filter.install_and_check(libc::SYS_lseek, [fd, 7, 0, 0, 0, 0], Expect::Denied);
            filter.install_and_check(libc::SYS_lseek, [fd, 8, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        }
    }
}

/// On a 64-bit architecture, a 64-bit argument takes one slot.
#[cfg(target_pointer_width = "64")]
#[test]
fn wide_args_64() {
    let fd = libc::c_ulong::MAX;
    let pread = Filter::new_native_deny(Syscall::Pread64, cond!(@3 == 0x1_0000_0002i64));
    let readahead = Filter::new_native_deny(Syscall::Readahead, cond!(@1 == 0x1_0000_0002i64 && @2 == 3usize));
    let fallocate = Filter::new_native_deny(Syscall::Fallocate, cond!(@1 == 1 && @2 == 0x1_0000_0002i64 && @3 == 0x3_0000_0004i64));
    let sync = Filter::new_native_deny(Syscall::SyncFileRange, cond!(@1 == 0x1_0000_0002i64 && @3 == 7u32));
    let fadvise = Filter::new_native_deny(Syscall::Fadvise64, cond!(@1 == 0x1_0000_0002i64 && @3 == 4));
    unsafe {
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 0x1_0000_0002, 0, 0], Expect::Denied);
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 2, 1, 0], Expect::Errno(libc::EBADF));
        readahead.install_and_check(libc::SYS_readahead, [fd, 0x1_0000_0002, 3, 0, 0, 0], Expect::Denied);
        readahead.install_and_check(libc::SYS_readahead, [fd, 2, 1, 3, 0, 0], Expect::Errno(libc::EBADF));
        fallocate.install_and_check(libc::SYS_fallocate, [fd, 1, 0x1_0000_0002, 0x3_0000_0004, 0, 0], Expect::Denied);
        fallocate.install_and_check(libc::SYS_fallocate, [fd, 1, 2, 1, 4, 3], Expect::Errno(libc::EBADF));
        sync.install_and_check(libc::SYS_sync_file_range, [fd, 0x1_0000_0002, 0, 7, 0, 0], Expect::Denied);
        sync.install_and_check(libc::SYS_sync_file_range, [fd, 2, 1, 0, 0, 7], Expect::Errno(libc::EBADF));
        fadvise.install_and_check(libc::SYS_fadvise64, [fd, 0x1_0000_0002, 0, 4, 0, 0], Expect::Denied);
        fadvise.install_and_check(libc::SYS_fadvise64, [fd, 2, 1, 0, 4, 0], Expect::Errno(libc::EBADF));
    }
}

/// On x86, a 64-bit argument takes the next two slots, low word first.
#[cfg(target_arch = "x86")]
#[test]
fn x86_wide_args() {
    let fd = libc::c_ulong::MAX;
    let pread = Filter::new_native_deny(Syscall::Pread64, cond!(@3 == 0x1_0000_0002i64));
    let readahead = Filter::new_native_deny(Syscall::Readahead, cond!(@1 == 0x1_0000_0002i64 && @2 == 3usize));
    let fallocate = Filter::new_native_deny(Syscall::Fallocate, cond!(@1 == 1 && @2 == 0x1_0000_0002i64 && @3 == 0x3_0000_0004i64));
    unsafe {
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 2, 1, 0], Expect::Denied);
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 2, 1, 9], Expect::Denied);
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 2, 0, 1], Expect::Errno(libc::EBADF));
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 1, 2, 0], Expect::Errno(libc::EBADF));
        readahead.install_and_check(libc::SYS_readahead, [fd, 2, 1, 3, 0, 0], Expect::Denied);
        readahead.install_and_check(libc::SYS_readahead, [fd, 0, 2, 1, 3, 0], Expect::Errno(libc::EBADF));
        fallocate.install_and_check(libc::SYS_fallocate, [fd, 1, 2, 1, 4, 3], Expect::Denied);
        fallocate.install_and_check(libc::SYS_fallocate, [fd, 1, 2, 1, 3, 4], Expect::Errno(libc::EBADF));
    }
}

/// On x86, arguments after two 64-bit ones reach the sixth slot.
#[cfg(target_arch = "x86")]
#[test]
fn x86_sixth_slot() {
    let fd = libc::c_ulong::MAX;
    let sync = Filter::new_native_deny(Syscall::SyncFileRange, cond!(@2 == 0x1_0000_0002i64 && @3 == 7u32));
    let fadvise64_64 = Filter::new_native_deny(Syscall::Fadvise64_64, cond!(@3 == 4));
    let fadvise64 = Filter::new_native_deny(Syscall::Fadvise64, cond!(@2 == 5usize && @3 == 4));
    unsafe {
        sync.install_and_check(libc::SYS_sync_file_range, [fd, 0, 0, 2, 1, 7], Expect::Denied);
        sync.install_and_check(libc::SYS_sync_file_range, [fd, 0, 0, 2, 1, 0], Expect::Errno(libc::EBADF));
        sync.install_and_check(libc::SYS_sync_file_range, [fd, 0, 2, 1, 7, 0], Expect::Errno(libc::EBADF));
        fadvise64_64.install_and_check(libc::SYS_fadvise64_64, [fd, 0, 0, 0, 0, 4], Expect::Denied);
        fadvise64_64.install_and_check(libc::SYS_fadvise64_64, [fd, 0, 0, 4, 0, 0], Expect::Errno(libc::EBADF));
        fadvise64.install_and_check(libc::SYS_fadvise64, [fd, 0, 0, 5, 4, 0], Expect::Denied);
        fadvise64.install_and_check(libc::SYS_fadvise64, [fd, 0, 0, 4, 5, 0], Expect::Errno(libc::EBADF));
    }
}

/// On x86, a signed 64-bit argument takes its sign from the high slot.
#[cfg(target_arch = "x86")]
#[test]
fn x86_wide_signed() {
    let fd = libc::c_ulong::MAX;
    let filter = Filter::new_native_deny(Syscall::Ftruncate64, cond!(@1 < 0i64));
    unsafe {
        filter.install_and_check(libc::SYS_ftruncate64, [fd, 0, 0x8000_0000, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_ftruncate64, [fd, 0, 0xffff_ffff, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_ftruncate64, [fd, 0xffff_ffff, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_ftruncate64, [fd, 0xffff_ffff, 0x7fff_ffff, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// On ARM, a 64-bit argument starts at the next even slot, skipping the one in between.
#[cfg(target_arch = "arm")]
#[test]
fn arm_wide_args() {
    let fd = libc::c_ulong::MAX;
    let pread = Filter::new_native_deny(Syscall::Pread64, cond!(@3 == 0x1_0000_0002i64));
    let readahead = Filter::new_native_deny(Syscall::Readahead, cond!(@1 == 0x1_0000_0002i64 && @2 == 3usize));
    let fallocate = Filter::new_native_deny(Syscall::Fallocate, cond!(@1 == 1 && @2 == 0x1_0000_0002i64 && @3 == 0x3_0000_0004i64));
    unsafe {
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 0, 2, 1], Expect::Denied);
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 0xdead, 2, 1], Expect::Denied);
        pread.install_and_check(libc::SYS_pread64, [fd, 0, 0, 2, 1, 0], Expect::Errno(libc::EBADF));
        readahead.install_and_check(libc::SYS_readahead, [fd, 0, 2, 1, 3, 0], Expect::Denied);
        readahead.install_and_check(libc::SYS_readahead, [fd, 0xdead, 2, 1, 3, 0], Expect::Denied);
        readahead.install_and_check(libc::SYS_readahead, [fd, 2, 1, 3, 0, 0], Expect::Errno(libc::EBADF));
        fallocate.install_and_check(libc::SYS_fallocate, [fd, 1, 2, 1, 4, 3], Expect::Denied);
        fallocate.install_and_check(libc::SYS_fallocate, [fd, 1, 2, 1, 3, 4], Expect::Errno(libc::EBADF));
    }
}

/// On ARM, the reordered `arm_fadvise64_64` and `sync_file_range2` need no padding.
#[cfg(target_arch = "arm")]
#[test]
fn arm_reordered() {
    let fd = libc::c_ulong::MAX;
    // The numbers in `arch/arm/tools/syscall.tbl`, which `libc` does not define.
    let arm_fadvise64_64: libc::c_long = 270;
    let sync_file_range2: libc::c_long = 341;
    let fadvise = Filter::new_native_deny(Syscall::ArmFadvise64_64, cond!(@1 == 4 && @3 == 0x1_0000_0002i64));
    let sync = Filter::new_native_deny(Syscall::ArmSyncFileRange, cond!(@1 == 7u32 && @3 == 0x1_0000_0002i64));
    unsafe {
        fadvise.install_and_check(arm_fadvise64_64, [fd, 4, 0, 0, 2, 1], Expect::Denied);
        fadvise.install_and_check(arm_fadvise64_64, [fd, 0, 0, 0, 2, 1], Expect::Errno(libc::EBADF));
        fadvise.install_and_check(arm_fadvise64_64, [fd, 4, 0, 0, 1, 2], Expect::Errno(libc::EBADF));
        sync.install_and_check(sync_file_range2, [fd, 7, 0, 0, 2, 1], Expect::Denied);
        sync.install_and_check(sync_file_range2, [fd, 7, 0, 0, 1, 2], Expect::Errno(libc::EBADF));
    }
}

/// On ARM, a signed 64-bit argument takes its sign from the high slot after the padding.
#[cfg(target_arch = "arm")]
#[test]
fn arm_wide_signed() {
    let fd = libc::c_ulong::MAX;
    let filter = Filter::new_native_deny(Syscall::Ftruncate64, cond!(@1 < 0i64));
    unsafe {
        filter.install_and_check(libc::SYS_ftruncate64, [fd, 0, 0, 0x8000_0000, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_ftruncate64, [fd, 0, 0, 0xffff_ffff, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_ftruncate64, [fd, 0, 0xffff_ffff, 0, 0, 0], Expect::Errno(libc::EBADF));
        filter.install_and_check(libc::SYS_ftruncate64, [fd, 0x8000_0000, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// An offset libc's `pread64` splits into words meets a test on the whole offset.
#[test]
fn libc_pread64() {
    let exact = Filter::new_native_deny(Syscall::Pread64, cond!(@3 == 0x1_0000_0002i64));
    let negative = Filter::new_native_deny(Syscall::Pread64, cond!(@3 < 0i64));
    let ebadf = Expect::Errno(libc::EBADF);
    for (filter, offset, expect) in [
        (&exact, 0x1_0000_0002, Expect::Denied),
        (&exact, 0x2, ebadf),
        (&exact, 0x1_0000_0000, ebadf),
        (&exact, 0x2_0000_0001, ebadf),
        (&negative, -1, Expect::Denied),
        (&negative, -0x1_0000_0000, Expect::Denied),
        (&negative, i64::MIN, Expect::Denied),
        (&negative, 0xffff_ffff, ebadf),
        (&negative, i64::MAX, ebadf),
    ] {
        let call = || (unsafe { libc::pread64(-1, std::ptr::null_mut(), 0, offset) } as _, Expect::errno());
        assert!(expect.matches(unsafe { filter.install_and_run(call) }), "pread64 at {offset:#x} should come back as {expect:?} under {filter:?}");
    }
}

/// A length libc's `ftruncate64` splits into words meets a test on the whole length.
#[test]
fn libc_ftruncate64() {
    let syscall = if cfg!(target_pointer_width = "64") { Syscall::Ftruncate } else { Syscall::Ftruncate64 };
    let exact = Filter::new_native_deny(syscall, cond!(@1 == 0x1_0000_0002i64));
    let negative = Filter::new_native_deny(syscall, cond!(@1 < 0i64));
    let ebadf = Expect::Errno(libc::EBADF);
    for (filter, length, expect) in [
        (&exact, 0x1_0000_0002, Expect::Denied),
        (&exact, 0x2, ebadf),
        (&exact, 0x2_0000_0001, ebadf),
        (&negative, -1, Expect::Denied),
        (&negative, -0x1_0000_0000, Expect::Denied),
        (&negative, 0xffff_ffff, ebadf),
        (&negative, 0x1_0000_0000, ebadf),
    ] {
        let call = || (unsafe { libc::ftruncate64(-1, length) } as _, Expect::errno());
        assert!(expect.matches(unsafe { filter.install_and_run(call) }), "ftruncate64 to {length:#x} should come back as {expect:?} under {filter:?}");
    }
}

/// libc's `readahead` passes a split offset and the count after it where the filter tests them.
#[test]
fn libc_readahead() {
    let filter = Filter::new_native_deny(Syscall::Readahead, cond!(@1 == 0x1_0000_0002i64 && @2 == 7usize));
    let ebadf = Expect::Errno(libc::EBADF);
    for (offset, count, expect) in [
        (0x1_0000_0002, 7, Expect::Denied),
        (0x2_0000_0001, 7, ebadf),
        (0x2, 7, ebadf),
        (0x1_0000_0002, 0, ebadf),
    ] {
        let call = || (unsafe { libc::readahead(-1, offset, count) } as _, Expect::errno());
        assert!(expect.matches(unsafe { filter.install_and_run(call) }), "readahead({offset:#x}, {count}) should come back as {expect:?}");
    }
}

/// libc's `fallocate64` passes its mode and two split values where the filter tests them.
#[test]
fn libc_fallocate64() {
    let filter = Filter::new_native_deny(Syscall::Fallocate, cond!(@1 == 1 && @2 == 0x1_0000_0002i64 && @3 == 0x3_0000_0004i64));
    let ebadf = Expect::Errno(libc::EBADF);
    for (mode, offset, len, expect) in [
        (1, 0x1_0000_0002, 0x3_0000_0004, Expect::Denied),
        (0, 0x1_0000_0002, 0x3_0000_0004, ebadf),
        (1, 0x3_0000_0004, 0x1_0000_0002, ebadf),
        (1, 0x2_0000_0001, 0x3_0000_0004, ebadf),
        (1, 0x1_0000_0002, 0x4_0000_0003, ebadf),
        (1, 0x1_0000_0002, 0x4, ebadf),
    ] {
        let call = || (unsafe { libc::fallocate64(-1, mode, offset, len) } as _, Expect::errno());
        assert!(expect.matches(unsafe { filter.install_and_run(call) }), "fallocate64({mode}, {offset:#x}, {len:#x}) should come back as {expect:?}");
    }
}

/// libc's `sync_file_range` reaches the filter with its flags after or, on ARM, before two split values.
#[test]
fn libc_sync_file_range() {
    let (syscall, flags_arg, offset_arg, nbytes_arg) = if cfg!(target_arch = "arm") {
        (Syscall::ArmSyncFileRange, 1, 2, 3)
    } else {
        (Syscall::SyncFileRange, 3, 1, 2)
    };
    let filter = Filter::new_native_deny(syscall, cond!({Expr::Var(flags_arg)} == 2u32 && {Expr::Var(offset_arg)} == 0x1_0000_0002i64 && {Expr::Var(nbytes_arg)} == 0x3_0000_0004i64));
    let ebadf = Expect::Errno(libc::EBADF);
    for (offset, nbytes, flags, expect) in [
        (0x1_0000_0002, 0x3_0000_0004, 2, Expect::Denied),
        (0x1_0000_0002, 0x3_0000_0004, 0, ebadf),
        (0x3_0000_0004, 0x1_0000_0002, 2, ebadf),
        (0x2_0000_0001, 0x3_0000_0004, 2, ebadf),
        (0x1_0000_0002, 0x4_0000_0003, 2, ebadf),
    ] {
        let call = || (unsafe { libc::sync_file_range(-1, offset, nbytes, flags) } as _, Expect::errno());
        assert!(expect.matches(unsafe { filter.install_and_run(call) }), "sync_file_range({offset:#x}, {nbytes:#x}, {flags}) should come back as {expect:?}");
    }
}

/// libc's `posix_fadvise64` reaches the filter with its advice after or, on ARM, before two split values.
#[test]
fn libc_posix_fadvise64() {
    let (syscall, advice_arg, offset_arg, len_arg) = if cfg!(target_arch = "arm") {
        (Syscall::ArmFadvise64_64, 1, 2, 3)
    } else if cfg!(target_arch = "x86") {
        (Syscall::Fadvise64_64, 3, 1, 2)
    } else {
        (Syscall::Fadvise64, 3, 1, 2)
    };
    // `fadvise64` on x86_64 takes its length as a `size_t`, the others as a `loff_t`.
    let len_ty = syscall.signature(Arch::native().unwrap())[len_arg as usize];
    let filter = Filter::new_native_deny(syscall, cond!({Expr::Var(advice_arg)} == 4 && {Expr::Var(offset_arg)} == 0x1_0000_0002i64 && {Expr::Var(len_arg)} == 0x3_0000_0004u64 as len_ty));
    let ebadf = Expect::Errno(libc::EBADF);
    for (offset, len, advice, expect) in [
        (0x1_0000_0002, 0x3_0000_0004, 4, Expect::Denied),
        (0x1_0000_0002, 0x3_0000_0004, 0, ebadf),
        (0x3_0000_0004, 0x1_0000_0002, 4, ebadf),
        (0x2_0000_0001, 0x3_0000_0004, 4, ebadf),
        (0x1_0000_0002, 0x4_0000_0003, 4, ebadf),
    ] {
        // posix_fadvise returns its error rather than setting errno.
        let call = || match unsafe { libc::posix_fadvise64(-1, offset, len, advice) } {
            0 => (0, 0),
            err => (-1, err),
        };
        assert!(expect.matches(unsafe { filter.install_and_run(call) }), "posix_fadvise64({offset:#x}, {len:#x}, {advice}) should come back as {expect:?}");
    }
}

/// The native numbers of syscalls every architecture has match `libc`'s `SYS_*`.
#[test]
fn native_numbers() {
    let native = Arch::native().unwrap();
    for (syscall, nr) in [
        (Syscall::Read, libc::SYS_read),
        (Syscall::Write, libc::SYS_write),
        (Syscall::Close, libc::SYS_close),
        (Syscall::Lseek, libc::SYS_lseek),
        (Syscall::Getpid, libc::SYS_getpid),
        (Syscall::Getppid, libc::SYS_getppid),
        (Syscall::Getuid, libc::SYS_getuid),
        (Syscall::Dup, libc::SYS_dup),
        (Syscall::Dup3, libc::SYS_dup3),
        (Syscall::Mprotect, libc::SYS_mprotect),
        (Syscall::Munmap, libc::SYS_munmap),
        (Syscall::Madvise, libc::SYS_madvise),
        (Syscall::Mremap, libc::SYS_mremap),
        (Syscall::Msync, libc::SYS_msync),
        (Syscall::Pread64, libc::SYS_pread64),
        (Syscall::Pwrite64, libc::SYS_pwrite64),
        (Syscall::Preadv, libc::SYS_preadv),
        (Syscall::Preadv2, libc::SYS_preadv2),
        (Syscall::Readahead, libc::SYS_readahead),
        (Syscall::Fallocate, libc::SYS_fallocate),
        (Syscall::Ftruncate, libc::SYS_ftruncate),
        (Syscall::Fchmod, libc::SYS_fchmod),
        (Syscall::Fchown, libc::SYS_fchown),
        (Syscall::Fchownat, libc::SYS_fchownat),
        (Syscall::Fcntl, libc::SYS_fcntl),
        (Syscall::Ioctl, libc::SYS_ioctl),
        (Syscall::Prctl, libc::SYS_prctl),
        (Syscall::Clone, libc::SYS_clone),
        (Syscall::Futex, libc::SYS_futex),
        (Syscall::Kill, libc::SYS_kill),
        (Syscall::Tkill, libc::SYS_tkill),
        (Syscall::Tgkill, libc::SYS_tgkill),
        (Syscall::Getpriority, libc::SYS_getpriority),
        (Syscall::Setpriority, libc::SYS_setpriority),
        (Syscall::Setresuid, libc::SYS_setresuid),
        (Syscall::Personality, libc::SYS_personality),
        (Syscall::Umask, libc::SYS_umask),
        (Syscall::Wait4, libc::SYS_wait4),
        (Syscall::Uname, libc::SYS_uname),
        (Syscall::Exit, libc::SYS_exit),
        (Syscall::ExitGroup, libc::SYS_exit_group),
        (Syscall::Socket, libc::SYS_socket),
        (Syscall::Accept4, libc::SYS_accept4),
        (Syscall::Sendfile, libc::SYS_sendfile),
        (Syscall::Splice, libc::SYS_splice),
        (Syscall::Tee, libc::SYS_tee),
        (Syscall::EpollPwait, libc::SYS_epoll_pwait),
        (Syscall::FanotifyMark, libc::SYS_fanotify_mark),
        (Syscall::ProcessVmReadv, libc::SYS_process_vm_readv),
        (Syscall::Getrandom, libc::SYS_getrandom),
        (Syscall::MemfdCreate, libc::SYS_memfd_create),
        (Syscall::Pipe2, libc::SYS_pipe2),
        (Syscall::Eventfd2, libc::SYS_eventfd2),
        (Syscall::Signalfd4, libc::SYS_signalfd4),
        (Syscall::Setns, libc::SYS_setns),
        (Syscall::Unshare, libc::SYS_unshare),
        (Syscall::Brk, libc::SYS_brk),
        (Syscall::SchedYield, libc::SYS_sched_yield),
        (Syscall::Getcpu, libc::SYS_getcpu),
    ] {
        assert_eq!(syscall.nr(native), Some(nr as _), "{syscall:?} on {native:?}");
    }
    assert_eq!(Syscall::Skip.nr(native), Some(-1));
}

/// The native numbers of syscalls only some architectures have match `libc`'s `SYS_*`.
#[test]
fn native_numbers_partial() {
    let native = Arch::native().unwrap();
    #[cfg(target_pointer_width = "64")]
    let expected = [
        (Syscall::Mmap, libc::SYS_mmap),
        (Syscall::Fadvise64, libc::SYS_fadvise64),
        (Syscall::SyncFileRange, libc::SYS_sync_file_range),
    ];
    #[cfg(target_arch = "x86")]
    let expected = [
        (Syscall::Mmap, libc::SYS_mmap),
        (Syscall::Mmap2, libc::SYS_mmap2),
        (Syscall::Fadvise64, libc::SYS_fadvise64),
        (Syscall::Fadvise64_64, libc::SYS_fadvise64_64),
        (Syscall::SyncFileRange, libc::SYS_sync_file_range),
        (Syscall::Ftruncate64, libc::SYS_ftruncate64),
        (Syscall::Truncate64, libc::SYS_truncate64),
        (Syscall::Fcntl64, libc::SYS_fcntl64),
        (Syscall::Chown32, libc::SYS_chown32),
        (Syscall::Setuid32, libc::SYS_setuid32),
        (Syscall::Socketcall, libc::SYS_socketcall),
        (Syscall::Ipc, libc::SYS_ipc),
    ];
    #[cfg(target_arch = "arm")]
    let expected = [
        (Syscall::Mmap2, libc::SYS_mmap2),
        (Syscall::Ftruncate64, libc::SYS_ftruncate64),
        (Syscall::Truncate64, libc::SYS_truncate64),
        (Syscall::Fcntl64, libc::SYS_fcntl64),
        (Syscall::Chown32, libc::SYS_chown32),
        (Syscall::Setuid32, libc::SYS_setuid32),
    ];
    for (syscall, nr) in expected {
        assert_eq!(syscall.nr(native), Some(nr as _), "{syscall:?} on {native:?}");
    }
}

/// Syscalls an architecture lacks have no number and no arguments there.
#[test]
fn absent_syscalls() {
    for (syscall, arch) in [
        (Syscall::Open, Arch::Aarch64),
        (Syscall::Mmap, Arch::Arm),
        (Syscall::Mmap2, Arch::X86_64),
        (Syscall::Ftruncate64, Arch::Aarch64),
        (Syscall::SyncFileRange, Arch::Arm),
        (Syscall::ArmSyncFileRange, Arch::X86),
        (Syscall::Fadvise64, Arch::Arm),
        (Syscall::Accept, Arch::X86),
        (Syscall::Socketcall, Arch::X86_64),
        (Syscall::Ipc, Arch::Arm),
    ] {
        assert_eq!(syscall.nr(arch), None, "{syscall:?} on {arch:?}");
        assert!(syscall.signature(arch).is_empty(), "{syscall:?} on {arch:?}");
    }
}

/// Signatures follow each architecture's entry point where the architectures disagree.
#[test]
fn signatures() {
    use PrimType::*;
    let cases: &[(Syscall, Arch, &[PrimType])] = &[
        // `old_mmap` takes a pointer to its arguments.
        (Syscall::Mmap, Arch::X86, &[Ptr]),
        (Syscall::Mmap, Arch::X86_64, &[UWord; 6]),
        (Syscall::Mmap2, Arch::Arm, &[UWord; 6]),
        // `CONFIG_CLONE_BACKWARDS` swaps the last two arguments everywhere but x86_64.
        (Syscall::Clone, Arch::X86_64, &[UWord, UWord, Ptr, Ptr, UWord]),
        (Syscall::Clone, Arch::X86, &[UWord, UWord, Ptr, UWord, Ptr]),
        (Syscall::Clone, Arch::Aarch64, &[UWord, UWord, Ptr, UWord, Ptr]),
        // The 16-bit uid calls in `kernel/uid16.c`.
        (Syscall::Chown, Arch::X86, &[Ptr, U(16), U(16)]),
        (Syscall::Chown, Arch::Arm, &[Ptr, U(16), U(16)]),
        (Syscall::Chown, Arch::X86_64, &[Ptr, U(32), U(32)]),
        (Syscall::Chown32, Arch::X86, &[Ptr, U(32), U(32)]),
        (Syscall::Setresuid, Arch::X86, &[U(16), U(16), U(16)]),
        (Syscall::Setresuid, Arch::Aarch64, &[U(32), U(32), U(32)]),
        (Syscall::Fchown, Arch::Arm, &[U(32), U(16), U(16)]),
        // `loff_t` stays one 64-bit argument on 32-bit architectures.
        (Syscall::Pread64, Arch::X86, &[U(32), Ptr, UWord, I(64)]),
        (Syscall::Pread64, Arch::Arm, &[U(32), Ptr, UWord, I(64)]),
        (Syscall::Ftruncate64, Arch::X86, &[U(32), I(64)]),
        (Syscall::Truncate64, Arch::Arm, &[Ptr, I(64)]),
        (Syscall::FanotifyMark, Arch::Arm, &[I(32), U(32), U(64), I(32), Ptr]),
        // `off_t` and `size_t` are words.
        (Syscall::Ftruncate, Arch::X86, &[U(32), IWord]),
        (Syscall::Lseek, Arch::Aarch64, &[U(32), IWord, U(32)]),
        (Syscall::Read, Arch::Arm, &[U(32), Ptr, UWord]),
        // arm64 has only `fadvise64_64`, under the `fadvise64` name.
        (Syscall::Fadvise64, Arch::X86_64, &[I(32), I(64), UWord, I(32)]),
        (Syscall::Fadvise64, Arch::Aarch64, &[I(32), I(64), I(64), I(32)]),
        (Syscall::Fadvise64_64, Arch::X86, &[I(32), I(64), I(64), I(32)]),
        // ARM moves the `int` arguments ahead of the `loff_t` ones.
        (Syscall::ArmFadvise64_64, Arch::Arm, &[I(32), I(32), I(64), I(64)]),
        (Syscall::ArmSyncFileRange, Arch::Arm, &[I(32), U(32), I(64), I(64)]),
        (Syscall::SyncFileRange, Arch::X86, &[I(32), I(64), I(64), U(32)]),
        (Syscall::Socketcall, Arch::X86, &[I(32), Ptr]),
        (Syscall::Getpid, Arch::Arm, &[]),
        (Syscall::Skip, Arch::X86_64, &[]),
    ];
    for &(syscall, arch, sig) in cases {
        assert_eq!(syscall.signature(arch), sig, "{syscall:?} on {arch:?}");
    }
}

/// Arithmetic on arguments wraps around at their type.
#[test]
fn arith() {
    let plus_one = Filter::new_native_deny(Syscall::Getpriority, cond!(@0 + 1 == 0));
    let minus_one = Filter::new_native_deny(Syscall::Dup, cond!(@0 - 1u32 > 0xffff_fff0u32));
    unsafe {
        plus_one.install_and_check(libc::SYS_getpriority, [-1i64 as libc::c_ulong, 0, 0, 0, 0, 0], Expect::Denied);
        plus_one.install_and_check(libc::SYS_getpriority, [0, 0, 0, 0, 0, 0], Expect::Ok);
        minus_one.install_and_check(libc::SYS_dup, [0xffff_fff5, 0, 0, 0, 0, 0], Expect::Denied);
        minus_one.install_and_check(libc::SYS_dup, [0x7fff_ffff, 0, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// A cast keeps the bits of an argument that fit the new type, and reads them as it.
#[test]
fn cast() {
    let fd = libc::c_ulong::MAX;
    let low_byte = Filter::new_native_deny(Syscall::Lseek, cond!(@1 as u8 == 0x44u8));
    let negative_short = Filter::new_native_deny(Syscall::Lseek, cond!(@1 as i16 < 0i16));
    unsafe {
        low_byte.install_and_check(libc::SYS_lseek, [fd, 0x144, 0, 0, 0, 0], Expect::Denied);
        low_byte.install_and_check(libc::SYS_lseek, [fd, 0x45, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
        negative_short.install_and_check(libc::SYS_lseek, [fd, 0x8000, 0, 0, 0, 0], Expect::Denied);
        negative_short.install_and_check(libc::SYS_lseek, [fd, 0x1_8000, 0, 0, 0, 0], Expect::Denied);
        negative_short.install_and_check(libc::SYS_lseek, [fd, 0x7fff, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// Two arguments compare with each other.
#[test]
fn arg_pair() {
    let filter = Filter::new_native_deny(Syscall::Lseek, cond!(@0 < @2));
    unsafe {
        filter.install_and_check(libc::SYS_lseek, [3, 0, 4, 0, 0, 0], Expect::Denied);
        filter.install_and_check(libc::SYS_lseek, [libc::c_ulong::MAX, 0, 0, 0, 0, 0], Expect::Errno(libc::EBADF));
    }
}

/// A constant compares with an argument when either type converts to the other.
#[test]
fn literal_types() {
    for ty in [I(32), I(16), I(64), U(16), U(8)] {
        assert!(Filter::with_rule(&[Arch::X86_64], Syscall::Getpriority, cond!(@0 < 1 as ty)).is_ok(), "{ty:?}");
    }
    for ty in [U(32), U(64), Ptr] {
        assert!(matches!(
            Filter::with_rule(&[Arch::X86_64], Syscall::Getpriority, cond!(@0 == 1 as ty)),
            Err(Error::Check(CheckError::CmpTypes {
                op: CmpOp::Eq, lhs: I(32), rhs,
            })) if rhs == ty,
        ), "{ty:?}");
    }
}

/// A constant on an unsigned argument must be unsigned, or signed and wider.
#[test]
fn unsigned_types() {
    for (syscall, i, ty, signed) in [
        (Syscall::Dup, 0, U(32), I(32)),
        (Syscall::Fchmod, 1, U(16), I(16)),
        (Syscall::Setresuid, 2, U(16), I(16)),
    ] {
        let archs = [Arch::X86, Arch::Arm];
        for lty in [ty, U(64), I(64)] {
            assert!(Filter::with_rule(&archs, syscall, cond!({Expr::Var(i)} >= 0xffff as lty)).is_ok(), "{syscall:?} {lty:?}");
        }
        assert!(matches!(
            Filter::with_rule(&archs, syscall, cond!({Expr::Var(i)} <= 1 as signed)),
            Err(Error::Check(CheckError::CmpTypes { op: CmpOp::Le, lhs, rhs, .. })) if lhs == ty && rhs == signed,
        ), "{syscall:?}");
    }
}

/// A constant on a word argument must convert to or from the word of every enabled
/// architecture.
#[test]
fn word_types() {
    // `off_t` is a signed word, which a `u32` fits only where the word is wider.
    let above = cond!(@1 == 0x8000_0000u32);
    assert!(Filter::with_rule(&[Arch::X86_64, Arch::Aarch64], Syscall::Lseek, above.clone()).is_ok());
    assert!(matches!(
        Filter::with_rule(&[Arch::X86_64, Arch::X86], Syscall::Lseek, above),
        Err(Error::Check(CheckError::CmpTypes { lhs: IWord, rhs: U(32), .. })),
    ));
    assert!(Filter::with_rule(&[Arch::X86_64, Arch::X86], Syscall::Lseek, cond!(@1 == -0x8000_0000)).is_ok());
    // A word converts both ways with the fixed-width type of its size.
    assert!(Filter::with_rule(&[Arch::Aarch64], Syscall::Mprotect, cond!(@1 == 0xffff_ffff_ffff_ffffu64)).is_ok());
    assert!(Filter::with_rule(&[Arch::Arm], Syscall::Mprotect, cond!(@1 == 0xffff_ffffu32)).is_ok());
    // A pointer compares only with a pointer.
    assert!(matches!(
        Filter::with_rule(&[Arch::X86], Syscall::Uname, cond!(@0 != 0usize)),
        Err(Error::Check(CheckError::CmpTypes { lhs: Ptr, rhs: UWord, .. })),
    ));
    assert!(Filter::with_rule(&[Arch::X86_64], Syscall::Uname, cond!(@0 != -1 as ptr)).is_ok());
}

/// A 64-bit argument takes 64-bit constants and narrower ones, even on a 32-bit architecture.
#[test]
fn wide_types() {
    let all = [Arch::X86, Arch::X86_64, Arch::Arm, Arch::Aarch64];
    for ty in [I(64), IWord, I(32), U(32)] {
        assert!(Filter::with_rule(&all, Syscall::Pread64, cond!(@3 < 1 as ty)).is_ok(), "{ty:?}");
    }
    let range = cond!(@2 >= 0x8000_0000i64 && @3 <= -1i64);
    assert!(Filter::with_rule(&all, Syscall::Fallocate, range).is_ok());
    assert!(Filter::with_rule(&[Arch::X86, Arch::Arm], Syscall::FanotifyMark, cond!(@2 > 0x1_0000_0000u64)).is_ok());
    assert!(Filter::with_rule(&[Arch::Arm], Syscall::Pread64, cond!(@3 & -1i64 == 0x1_0000_0000i64)).is_ok());
}

/// A mask must have the argument's own type, since bitwise operations do not convert.
#[test]
fn mask_types() {
    assert!(Filter::with_rule(&[Arch::X86_64], Syscall::Getpriority, cond!(@0 & -1 == -0x8000_0000)).is_ok());
    for ty in [U(32), I(64), I(16)] {
        assert!(matches!(
            Filter::with_rule(&[Arch::X86_64], Syscall::Getpriority, cond!(@0 & 0xff as ty == 0)),
            Err(Error::Check(CheckError::BinOpTypes { op: BinOp::And, lhs: I(32), rhs, .. })) if rhs == ty,
        ), "{ty:?}");
    }
    // A word and a fixed-width type of its size are distinct types.
    assert!(Filter::with_rule(&[Arch::X86_64], Syscall::Lseek, cond!(@1 & -1isize == -1isize)).is_ok());
    assert!(matches!(
        Filter::with_rule(&[Arch::X86_64], Syscall::Lseek, cond!(@1 & -1i64 == 0i64)),
        Err(Error::Check(CheckError::BinOpTypes { lhs: IWord, rhs: I(64), .. })),
    ));
}

/// A pointer argument turns down ordering and bitwise operations, and takes the rest.
#[test]
fn ptr_ops() {
    for (on_ptr, on_ints) in [
        (cond!(@0 < 0 as ptr), cond!(@0 < 0u32 && @2 < 0usize)),
        (cond!(@0 <= 0 as ptr), cond!(@0 <= 0u32 && @2 <= 0usize)),
        (cond!(@0 > 0 as ptr), cond!(@0 > 0u32 && @2 > 0usize)),
        (cond!(@0 >= 0 as ptr), cond!(@0 >= 0u32 && @2 >= 0usize)),
    ] {
        assert!(matches!(
            Filter::with_rule(&[Arch::X86_64], Syscall::Uname, on_ptr),
            Err(Error::Check(CheckError::CmpTypes { lhs: Ptr, rhs: Ptr, .. })),
        ));
        assert!(Filter::with_rule(&[Arch::X86_64], Syscall::Read, on_ints).is_ok());
    }
    assert!(matches!(
        Filter::with_rule(&[Arch::X86], Syscall::Uname, cond!(@0 & 0xfff as ptr == 0 as ptr)),
        Err(Error::Check(CheckError::BinOpTypes { op: BinOp::And, lhs: Ptr, rhs: Ptr, .. })),
    ));
    assert!(matches!(
        Filter::with_rule(&[Arch::X86], Syscall::Uname, cond!(@0 + 1 as ptr == 0 as ptr)),
        Err(Error::Check(CheckError::BinOpTypes { op: BinOp::Add, lhs: Ptr, rhs: Ptr, .. })),
    ));
    for cond in [
        cond!(@0 == 0 as ptr),
        cond!(@0 != 0 as ptr),
        cond!(@0 as usize & 0xfffusize == 0usize),
    ] {
        assert!(Filter::with_rule(&[Arch::X86], Syscall::Uname, cond).is_ok());
    }
}

/// The last argument of each signature can be tested, and the one after it cannot.
#[test]
fn arg_count() {
    for (syscall, arch, total) in [
        (Syscall::Mmap2, Arch::X86, 6),
        (Syscall::Mmap, Arch::X86, 1),
        (Syscall::Clone, Arch::X86_64, 5),
        (Syscall::Pread64, Arch::Arm, 4),
        (Syscall::SyncFileRange, Arch::X86, 4),
        (Syscall::Uname, Arch::Aarch64, 1),
    ] {
        assert!(Filter::with_rule(&[arch], syscall, cond!({Expr::Var(total - 1)} == {Expr::Var(total - 1)})).is_ok(), "{syscall:?}");
        assert!(matches!(
            Filter::with_rule(&[arch], syscall, cond!({Expr::Var(total)} == {Expr::Var(total)})),
            Err(Error::Check(CheckError::InvalidArg { given, total: t })) if given == total && t == total,
        ), "{syscall:?}");
    }
}

/// A syscall an enabled architecture lacks takes a rule, but no argument tests.
#[test]
fn absent_syscall_rule() {
    assert!(Filter::with_rule(&[Arch::Aarch64], Syscall::Open, Cond::True).is_ok());
    assert!(matches!(
        Filter::with_rule(&[Arch::Aarch64], Syscall::Open, cond!(@0 == @0)),
        Err(Error::Check(CheckError::InvalidArg { given: 0, total: 0 })),
    ));
    assert!(matches!(
        Filter::with_rule(&[Arch::X86_64, Arch::Aarch64], Syscall::Open, cond!(@0 == @0)),
        Err(Error::Check(CheckError::IncompatSigs)),
    ));
    assert!(matches!(
        Filter::with_rule(&[Arch::X86, Arch::Arm], Syscall::Mmap, cond!(@0 == @0)),
        Err(Error::Check(CheckError::IncompatSigs)),
    ));
}

/// Argument tests need the syscall's signature to agree on every enabled architecture.
#[test]
fn incompat_sigs() {
    for (syscall, archs) in [
        (Syscall::Clone, [Arch::X86_64, Arch::Aarch64]),
        (Syscall::Clone, [Arch::X86, Arch::X86_64]),
        (Syscall::Chown, [Arch::X86, Arch::X86_64]),
        (Syscall::Setresuid, [Arch::Arm, Arch::Aarch64]),
        (Syscall::Fadvise64, [Arch::X86_64, Arch::Aarch64]),
        (Syscall::Chown32, [Arch::Arm, Arch::X86_64]),
    ] {
        assert!(Filter::with_rule(&archs, syscall, Cond::True).is_ok(), "{syscall:?}");
        assert!(matches!(
            Filter::with_rule(&archs, syscall, cond!(@0 == @0)),
            Err(Error::Check(CheckError::IncompatSigs)),
        ), "{syscall:?}");
    }
    for (syscall, archs) in [
        (Syscall::Clone, [Arch::X86, Arch::Aarch64]),
        (Syscall::Chown, [Arch::X86, Arch::Arm]),
        (Syscall::Fadvise64, [Arch::X86, Arch::X86_64]),
        (Syscall::Pread64, [Arch::X86, Arch::Aarch64]),
    ] {
        assert!(Filter::with_rule(&archs, syscall, cond!(@0 == @0)).is_ok(), "{syscall:?}");
    }
}

/// Argument tests need the syscall's signature to agree only on the architectures their rule is limited to.
#[test]
fn incompat_sigs_on_archs() {
    for (syscall, archs) in [
        (Syscall::Clone, [Arch::X86_64, Arch::Aarch64]),
        (Syscall::Chown, [Arch::X86, Arch::X86_64]),
        (Syscall::Setresuid, [Arch::Arm, Arch::Aarch64]),
    ] {
        let mut filter = Filter::with_rule(&archs, syscall, Cond::True).unwrap();
        filter.add_rule_on_archs(Expect::DENY, syscall, cond!(@0 == @0), &archs[..1]).unwrap();
        filter.add_rule_exact_on_archs(Expect::DENY, syscall, cond!(@0 == @0), &archs[1..]).unwrap();
        assert!(matches!(
            filter.add_rule_on_archs(Expect::DENY, syscall, cond!(@0 == @0), &archs),
            Err(Error::Check(CheckError::IncompatSigs)),
        ), "{syscall:?}");
    }
    let mut filter = Filter::with_rule(&[Arch::X86_64, Arch::Aarch64], Syscall::Getpid, Cond::True).unwrap();
    assert!(matches!(
        filter.add_rule_on_archs(Expect::DENY, Syscall::Open, cond!(@0 == @0), &[Arch::Aarch64]),
        Err(Error::Check(CheckError::InvalidArg { given: 0, total: 0 })),
    ));
    filter.add_rule_on_archs(Expect::DENY, Syscall::Open, cond!(@0 == @0), &[Arch::X86_64]).unwrap();
}

/// Adding an architecture leaves alone the rules limited to other architectures.
#[test]
fn add_arch_skips_limited_rules() {
    let mut filter = Filter::with_rule(&[Arch::X86], Syscall::Getpid, Cond::True).unwrap();
    filter.add_rule_on_archs(Expect::DENY, Syscall::Chown, cond!(@1 == 0u16), &[Arch::X86]).unwrap();
    filter.add_arch(Arch::X86_64).unwrap();
}

/// Adding an architecture rechecks the argument tests already in the filter.
#[test]
fn add_arch_rechecks() {
    let mut filter = Filter::with_rule(&[Arch::X86], Syscall::Chown, cond!(@1 == 0u16)).unwrap();
    assert!(matches!(filter.add_arch(Arch::X86_64), Err(Error::Check(CheckError::IncompatSigs))));
    filter.add_arch(Arch::Arm).unwrap();

    let mut filter = Filter::with_rule(&[], Syscall::Lseek, cond!(@1 == 0x8000_0000u32)).unwrap();
    filter.add_arch(Arch::X86_64).unwrap();
    assert!(matches!(
        filter.add_arch(Arch::X86),
        Err(Error::Check(CheckError::CmpTypes { lhs: IWord, rhs: U(32), .. })),
    ));
    filter.add_arch(Arch::Aarch64).unwrap();
}

/// Multiplexed syscalls take argument tests only in exact rules.
#[test]
fn mux_conds() {
    for syscall in [Syscall::Socket, Syscall::Accept4, Syscall::Semget, Syscall::Shmat] {
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        assert!(matches!(
            filter.add_rule(Expect::DENY, syscall, cond!(@0 == @0)),
            Err(Error::Check(CheckError::InvalidMuxConditions)),
        ), "{syscall:?}");
        filter.add_rule(Expect::DENY, syscall, Cond::True).unwrap();
        filter.add_rule_exact(Expect::DENY, syscall, cond!(@0 == @0)).unwrap();
    }
}
