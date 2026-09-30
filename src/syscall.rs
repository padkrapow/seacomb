#[allow(unused_imports)]
use vstd::prelude::*;

/// Defines a syscall enum and its `Syscall` impl from `#[name]`, `#[on]`, and `#[mux]` annotations.
///
/// A `#[mux]` condition has the form `@n & mask == val`, with both literals typed as argument
/// `n` of the multiplexer.
#[macro_export]
macro_rules! impl_syscall {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $(
                #[name($sname:literal)]
                $( #[on($arch:ident, $nr:expr $(, $ty:ident $(($width:literal))?)*)] )*
                $( #[mux($march:ident, $mux:ident, @ $n:literal & $mask:literal == $val:literal)] )*
                $variant:ident
            ),* $(,)?
        }
    ) => {
        ::vstd::prelude::verus! {
            $(#[$meta])*
            $vis enum $name {
                $( $variant, )*
            }

            impl $crate::Syscall for $name {
                #[allow(unreachable_patterns)]
                #[verifier::opaque]
                open spec fn spec_nr(self, arch: $crate::Arch) -> Option<i32> {
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( $crate::Arch::$arch => Some(($nr) as i32), )*
                                _ => None,
                            },
                        )*
                    }
                }

                /// Argument types on `arch`, empty if the syscall does not exist there.
                #[allow(unreachable_patterns)]
                #[verifier::opaque]
                open spec fn spec_signature(self, arch: $crate::Arch) -> ::vstd::prelude::Seq<$crate::PrimType> {
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( $crate::Arch::$arch => ::vstd::prelude::seq![$( $crate::PrimType::$ty $(($width))? ),*], )*
                                _ => ::vstd::prelude::Seq::empty(),
                            },
                        )*
                    }
                }

                #[allow(unreachable_patterns)]
                #[verifier::opaque]
                open spec fn spec_mux(self, arch: $crate::Arch) -> Option<(Self, $crate::Cond)> {
                    let entry: Option<(Self, u32, i64, i64)> = match self {
                        $(
                            $name::$variant => match arch {
                                $( $crate::Arch::$march => Some(($name::$mux, $n, $mask, $val)), )*
                                _ => None,
                            },
                        )*
                    };
                    match entry {
                        Some((mux, n, mask, val)) => {
                            let sig = $crate::Syscall::spec_signature(mux, arch);
                            // An out-of-range argument fails `Cond::wf` whatever its type, so any type fills in.
                            let ty = if n < sig.len() { sig[n as int] } else { $crate::PrimType::Ptr };
                            Some((mux, $crate::Cond::Cmp($crate::CmpOp::Eq,
                                ::std::sync::Arc::new($crate::Expr::BinOp($crate::BinOp::And,
                                    ::std::sync::Arc::new($crate::Expr::Var(n)),
                                    ::std::sync::Arc::new($crate::Expr::Lit(mask, ty)))),
                                ::std::sync::Arc::new($crate::Expr::Lit(val, ty)))))
                        }
                        None => None,
                    }
                }

                #[allow(unreachable_patterns)]
                fn nr(self, arch: $crate::Arch) -> (res: Option<i32>) {
                    reveal(<$name as $crate::Syscall>::spec_nr);
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( $crate::Arch::$arch => Some(($nr) as i32), )*
                                _ => None,
                            },
                        )*
                    }
                }

                #[allow(unreachable_patterns)]
                fn signature(self, arch: $crate::Arch) -> (res: &'static [$crate::PrimType]) {
                    reveal(<$name as $crate::Syscall>::spec_signature);
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( $crate::Arch::$arch => &[$( $crate::PrimType::$ty $(($width))? ),*], )*
                                _ => &[],
                            },
                        )*
                    }
                }

                #[verifier::external_body]
                fn lookup(name: &str) -> Option<Self> {
                    let names: &[(&str, $name)] = &[ $( ($sname, $name::$variant), )* ];
                    let name = name.as_bytes();
                    let mut i = 0;
                    while i < names.len() {
                        let cand = names[i].0.as_bytes();
                        let mut j = 0;
                        while j < name.len() && j < cand.len() && name[j] == cand[j] {
                            j += 1;
                        }
                        if j == name.len() && j == cand.len() {
                            return Some(names[i].1);
                        }
                        i += 1;
                    }
                    None
                }

                #[allow(unreachable_patterns)]
                fn mux(self, arch: $crate::Arch) -> (res: Option<(Self, $crate::Cond)>) {
                    reveal(<$name as $crate::Syscall>::spec_mux);
                    let entry: Option<(Self, u32, i64, i64)> = match self {
                        $(
                            $name::$variant => match arch {
                                $( $crate::Arch::$march => Some(($name::$mux, $n, $mask, $val)), )*
                                _ => None,
                            },
                        )*
                    };
                    match entry {
                        Some((mux, n, mask, val)) => {
                            let sig = $crate::Syscall::signature(mux, arch);
                            let ty = if (n as usize) < sig.len() { sig[n as usize] } else { $crate::PrimType::Ptr };
                            Some((mux, $crate::Cond::Cmp($crate::CmpOp::Eq,
                                ::std::sync::Arc::new($crate::Expr::BinOp($crate::BinOp::And,
                                    ::std::sync::Arc::new($crate::Expr::Var(n)),
                                    ::std::sync::Arc::new($crate::Expr::Lit(mask, ty)))),
                                ::std::sync::Arc::new($crate::Expr::Lit(val, ty)))))
                        }
                        None => None,
                    }
                }
            }
        }

        impl ::std::fmt::Display for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                f.write_str(match self {
                    $( $name::$variant => $sname, )*
                })
            }
        }
    };
}

impl_syscall! {
    /// All syscall symbols from Linux v7.0.
    ///
    /// Syscall numbers:
    /// [x86](https://github.com/torvalds/linux/blob/v7.0/arch/x86/entry/syscalls/syscall_32.tbl),
    /// [x86_64](https://github.com/torvalds/linux/blob/v7.0/arch/x86/entry/syscalls/syscall_64.tbl),
    /// [ARM](https://github.com/torvalds/linux/blob/v7.0/arch/arm/tools/syscall.tbl)
    /// (and [ARM-specific](https://github.com/torvalds/linux/blob/v7.0/arch/arm/include/uapi/asm/unistd.h)),
    /// [AArch64](https://github.com/torvalds/linux/blob/v7.0/scripts/syscall.tbl)
    /// (with [ABI selection](https://github.com/torvalds/linux/blob/v7.0/arch/arm64/kernel/Makefile.syscalls)).
    ///
    /// Argument types: each entry point's C definition
    /// ([`SYSCALL_DEFINEx`](https://github.com/torvalds/linux/blob/v7.0/include/linux/syscalls.h)),
    /// with 64-bit arguments unsplit
    /// (x86's [`ia32_*` wrappers](https://github.com/torvalds/linux/blob/v7.0/arch/x86/kernel/sys_ia32.c) and `SC_ARG64`).
    ///
    /// Multiplexed calls: `SYS_*` in `linux/net.h` for `socketcall`, and `linux/ipc.h` for `ipc`,
    /// which dispatches on the low 16 bits of its call number.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[non_exhaustive]
    pub enum SyscallLinuxV7 {
        // A special syscall to indicate it has been skipped.
        #[name("skip")]
        #[on(X86, -1)]
        #[on(X86_64, -1)]
        #[on(Arm, -1)]
        #[on(Aarch64, -1)]
        Skip,
        #[name("accept")]
        #[on(X86_64, 43, I(32), Ptr, Ptr)]
        #[on(Arm, 285, I(32), Ptr, Ptr)]
        #[on(Aarch64, 202, I(32), Ptr, Ptr)]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 5)]
        Accept,
        #[name("accept4")]
        #[on(X86, 364, I(32), Ptr, Ptr, I(32))]
        #[on(X86_64, 288, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 366, I(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 242, I(32), Ptr, Ptr, I(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 18)]
        Accept4,
        #[name("access")]
        #[on(X86, 33, Ptr, I(32))]
        #[on(X86_64, 21, Ptr, I(32))]
        #[on(Arm, 33, Ptr, I(32))]
        Access,
        #[name("acct")]
        #[on(X86, 51, Ptr)]
        #[on(X86_64, 163, Ptr)]
        #[on(Arm, 51, Ptr)]
        #[on(Aarch64, 89, Ptr)]
        Acct,
        #[name("add_key")]
        #[on(X86, 286, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(X86_64, 248, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Arm, 309, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Aarch64, 217, Ptr, Ptr, Ptr, UWord, I(32))]
        AddKey,
        #[name("adjtimex")]
        #[on(X86, 124, Ptr)]
        #[on(X86_64, 159, Ptr)]
        #[on(Arm, 124, Ptr)]
        #[on(Aarch64, 171, Ptr)]
        Adjtimex,
        #[name("afs_syscall")]
        #[on(X86, 137)]
        #[on(X86_64, 183)]
        AfsSyscall,
        #[name("alarm")]
        #[on(X86, 27, U(32))]
        #[on(X86_64, 37, U(32))]
        Alarm,
        #[name("arch_prctl")]
        #[on(X86, 384, I(32), UWord)]
        #[on(X86_64, 158, I(32), UWord)]
        ArchPrctl,
        #[name("arm_fadvise64_64")]
        #[on(Arm, 270, I(32), I(32), I(64), I(64))]
        ArmFadvise64_64,
        #[name("arm_sync_file_range")]
        #[on(Arm, 341, I(32), U(32), I(64), I(64))]
        ArmSyncFileRange,
        #[name("bdflush")]
        #[on(X86, 134)]
        #[on(Arm, 134)]
        Bdflush,
        #[name("bind")]
        #[on(X86, 361, I(32), Ptr, I(32))]
        #[on(X86_64, 49, I(32), Ptr, I(32))]
        #[on(Arm, 282, I(32), Ptr, I(32))]
        #[on(Aarch64, 200, I(32), Ptr, I(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 2)]
        Bind,
        #[name("bpf")]
        #[on(X86, 357, I(32), Ptr, U(32))]
        #[on(X86_64, 321, I(32), Ptr, U(32))]
        #[on(Arm, 386, I(32), Ptr, U(32))]
        #[on(Aarch64, 280, I(32), Ptr, U(32))]
        Bpf,
        #[name("break")]
        #[on(X86, 17)]
        Break,
        #[name("breakpoint")]
        #[on(Arm, 983041)]
        Breakpoint,
        #[name("brk")]
        #[on(X86, 45, UWord)]
        #[on(X86_64, 12, UWord)]
        #[on(Arm, 45, UWord)]
        #[on(Aarch64, 214, UWord)]
        Brk,
        #[name("cacheflush")]
        #[on(Arm, 983042, UWord, UWord, I(32))]
        Cacheflush,
        #[name("cachestat")]
        #[on(X86, 451, U(32), Ptr, Ptr, U(32))]
        #[on(X86_64, 451, U(32), Ptr, Ptr, U(32))]
        #[on(Arm, 451, U(32), Ptr, Ptr, U(32))]
        #[on(Aarch64, 451, U(32), Ptr, Ptr, U(32))]
        Cachestat,
        #[name("capget")]
        #[on(X86, 184, Ptr, Ptr)]
        #[on(X86_64, 125, Ptr, Ptr)]
        #[on(Arm, 184, Ptr, Ptr)]
        #[on(Aarch64, 90, Ptr, Ptr)]
        Capget,
        #[name("capset")]
        #[on(X86, 185, Ptr, Ptr)]
        #[on(X86_64, 126, Ptr, Ptr)]
        #[on(Arm, 185, Ptr, Ptr)]
        #[on(Aarch64, 91, Ptr, Ptr)]
        Capset,
        #[name("chdir")]
        #[on(X86, 12, Ptr)]
        #[on(X86_64, 80, Ptr)]
        #[on(Arm, 12, Ptr)]
        #[on(Aarch64, 49, Ptr)]
        Chdir,
        #[name("chmod")]
        #[on(X86, 15, Ptr, U(16))]
        #[on(X86_64, 90, Ptr, U(16))]
        #[on(Arm, 15, Ptr, U(16))]
        Chmod,
        #[name("chown")]
        #[on(X86, 182, Ptr, U(16), U(16))]
        #[on(X86_64, 92, Ptr, U(32), U(32))]
        #[on(Arm, 182, Ptr, U(16), U(16))]
        Chown,
        #[name("chown32")]
        #[on(X86, 212, Ptr, U(32), U(32))]
        #[on(Arm, 212, Ptr, U(32), U(32))]
        Chown32,
        #[name("chroot")]
        #[on(X86, 61, Ptr)]
        #[on(X86_64, 161, Ptr)]
        #[on(Arm, 61, Ptr)]
        #[on(Aarch64, 51, Ptr)]
        Chroot,
        #[name("clock_adjtime")]
        #[on(X86, 343, I(32), Ptr)]
        #[on(X86_64, 305, I(32), Ptr)]
        #[on(Arm, 372, I(32), Ptr)]
        #[on(Aarch64, 266, I(32), Ptr)]
        ClockAdjtime,
        #[name("clock_adjtime64")]
        #[on(X86, 405, I(32), Ptr)]
        #[on(Arm, 405, I(32), Ptr)]
        ClockAdjtime64,
        #[name("clock_getres")]
        #[on(X86, 266, I(32), Ptr)]
        #[on(X86_64, 229, I(32), Ptr)]
        #[on(Arm, 264, I(32), Ptr)]
        #[on(Aarch64, 114, I(32), Ptr)]
        ClockGetres,
        #[name("clock_getres_time64")]
        #[on(X86, 406, I(32), Ptr)]
        #[on(Arm, 406, I(32), Ptr)]
        ClockGetresTime64,
        #[name("clock_gettime")]
        #[on(X86, 265, I(32), Ptr)]
        #[on(X86_64, 228, I(32), Ptr)]
        #[on(Arm, 263, I(32), Ptr)]
        #[on(Aarch64, 113, I(32), Ptr)]
        ClockGettime,
        #[name("clock_gettime64")]
        #[on(X86, 403, I(32), Ptr)]
        #[on(Arm, 403, I(32), Ptr)]
        ClockGettime64,
        #[name("clock_nanosleep")]
        #[on(X86, 267, I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 230, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 265, I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 115, I(32), I(32), Ptr, Ptr)]
        ClockNanosleep,
        #[name("clock_nanosleep_time64")]
        #[on(X86, 407, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 407, I(32), I(32), Ptr, Ptr)]
        ClockNanosleepTime64,
        #[name("clock_settime")]
        #[on(X86, 264, I(32), Ptr)]
        #[on(X86_64, 227, I(32), Ptr)]
        #[on(Arm, 262, I(32), Ptr)]
        #[on(Aarch64, 112, I(32), Ptr)]
        ClockSettime,
        #[name("clock_settime64")]
        #[on(X86, 404, I(32), Ptr)]
        #[on(Arm, 404, I(32), Ptr)]
        ClockSettime64,
        #[name("clone")]
        #[on(X86, 120, UWord, UWord, Ptr, UWord, Ptr)]
        #[on(X86_64, 56, UWord, UWord, Ptr, Ptr, UWord)]
        #[on(Arm, 120, UWord, UWord, Ptr, UWord, Ptr)]
        #[on(Aarch64, 220, UWord, UWord, Ptr, UWord, Ptr)]
        Clone,
        #[name("clone3")]
        #[on(X86, 435, Ptr, UWord)]
        #[on(X86_64, 435, Ptr, UWord)]
        #[on(Arm, 435, Ptr, UWord)]
        #[on(Aarch64, 435, Ptr, UWord)]
        Clone3,
        #[name("close")]
        #[on(X86, 6, U(32))]
        #[on(X86_64, 3, U(32))]
        #[on(Arm, 6, U(32))]
        #[on(Aarch64, 57, U(32))]
        Close,
        #[name("close_range")]
        #[on(X86, 436, U(32), U(32), U(32))]
        #[on(X86_64, 436, U(32), U(32), U(32))]
        #[on(Arm, 436, U(32), U(32), U(32))]
        #[on(Aarch64, 436, U(32), U(32), U(32))]
        CloseRange,
        #[name("connect")]
        #[on(X86, 362, I(32), Ptr, I(32))]
        #[on(X86_64, 42, I(32), Ptr, I(32))]
        #[on(Arm, 283, I(32), Ptr, I(32))]
        #[on(Aarch64, 203, I(32), Ptr, I(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 3)]
        Connect,
        #[name("copy_file_range")]
        #[on(X86, 377, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(X86_64, 326, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(Arm, 391, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(Aarch64, 285, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        CopyFileRange,
        #[name("creat")]
        #[on(X86, 8, Ptr, U(16))]
        #[on(X86_64, 85, Ptr, U(16))]
        #[on(Arm, 8, Ptr, U(16))]
        Creat,
        #[name("create_module")]
        #[on(X86, 127)]
        #[on(X86_64, 174)]
        CreateModule,
        #[name("delete_module")]
        #[on(X86, 129, Ptr, U(32))]
        #[on(X86_64, 176, Ptr, U(32))]
        #[on(Arm, 129, Ptr, U(32))]
        #[on(Aarch64, 106, Ptr, U(32))]
        DeleteModule,
        #[name("dup")]
        #[on(X86, 41, U(32))]
        #[on(X86_64, 32, U(32))]
        #[on(Arm, 41, U(32))]
        #[on(Aarch64, 23, U(32))]
        Dup,
        #[name("dup2")]
        #[on(X86, 63, U(32), U(32))]
        #[on(X86_64, 33, U(32), U(32))]
        #[on(Arm, 63, U(32), U(32))]
        Dup2,
        #[name("dup3")]
        #[on(X86, 330, U(32), U(32), I(32))]
        #[on(X86_64, 292, U(32), U(32), I(32))]
        #[on(Arm, 358, U(32), U(32), I(32))]
        #[on(Aarch64, 24, U(32), U(32), I(32))]
        Dup3,
        #[name("epoll_create")]
        #[on(X86, 254, I(32))]
        #[on(X86_64, 213, I(32))]
        #[on(Arm, 250, I(32))]
        EpollCreate,
        #[name("epoll_create1")]
        #[on(X86, 329, I(32))]
        #[on(X86_64, 291, I(32))]
        #[on(Arm, 357, I(32))]
        #[on(Aarch64, 20, I(32))]
        EpollCreate1,
        #[name("epoll_ctl")]
        #[on(X86, 255, I(32), I(32), I(32), Ptr)]
        #[on(X86_64, 233, I(32), I(32), I(32), Ptr)]
        #[on(Arm, 251, I(32), I(32), I(32), Ptr)]
        #[on(Aarch64, 21, I(32), I(32), I(32), Ptr)]
        EpollCtl,
        #[name("epoll_ctl_old")]
        #[on(X86_64, 214)]
        EpollCtlOld,
        #[name("epoll_pwait")]
        #[on(X86, 319, I(32), Ptr, I(32), I(32), Ptr, UWord)]
        #[on(X86_64, 281, I(32), Ptr, I(32), I(32), Ptr, UWord)]
        #[on(Arm, 346, I(32), Ptr, I(32), I(32), Ptr, UWord)]
        #[on(Aarch64, 22, I(32), Ptr, I(32), I(32), Ptr, UWord)]
        EpollPwait,
        #[name("epoll_pwait2")]
        #[on(X86, 441, I(32), Ptr, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 441, I(32), Ptr, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 441, I(32), Ptr, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 441, I(32), Ptr, I(32), Ptr, Ptr, UWord)]
        EpollPwait2,
        #[name("epoll_wait")]
        #[on(X86, 256, I(32), Ptr, I(32), I(32))]
        #[on(X86_64, 232, I(32), Ptr, I(32), I(32))]
        #[on(Arm, 252, I(32), Ptr, I(32), I(32))]
        EpollWait,
        #[name("epoll_wait_old")]
        #[on(X86_64, 215)]
        EpollWaitOld,
        #[name("eventfd")]
        #[on(X86, 323, U(32))]
        #[on(X86_64, 284, U(32))]
        #[on(Arm, 351, U(32))]
        Eventfd,
        #[name("eventfd2")]
        #[on(X86, 328, U(32), I(32))]
        #[on(X86_64, 290, U(32), I(32))]
        #[on(Arm, 356, U(32), I(32))]
        #[on(Aarch64, 19, U(32), I(32))]
        Eventfd2,
        #[name("execve")]
        #[on(X86, 11, Ptr, Ptr, Ptr)]
        #[on(X86_64, 59, Ptr, Ptr, Ptr)]
        #[on(Arm, 11, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 221, Ptr, Ptr, Ptr)]
        Execve,
        #[name("execveat")]
        #[on(X86, 358, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(X86_64, 322, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(Arm, 387, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(Aarch64, 281, I(32), Ptr, Ptr, Ptr, I(32))]
        Execveat,
        #[name("exit")]
        #[on(X86, 1, I(32))]
        #[on(X86_64, 60, I(32))]
        #[on(Arm, 1, I(32))]
        #[on(Aarch64, 93, I(32))]
        Exit,
        #[name("exit_group")]
        #[on(X86, 252, I(32))]
        #[on(X86_64, 231, I(32))]
        #[on(Arm, 248, I(32))]
        #[on(Aarch64, 94, I(32))]
        ExitGroup,
        #[name("faccessat")]
        #[on(X86, 307, I(32), Ptr, I(32))]
        #[on(X86_64, 269, I(32), Ptr, I(32))]
        #[on(Arm, 334, I(32), Ptr, I(32))]
        #[on(Aarch64, 48, I(32), Ptr, I(32))]
        Faccessat,
        #[name("faccessat2")]
        #[on(X86, 439, I(32), Ptr, I(32), I(32))]
        #[on(X86_64, 439, I(32), Ptr, I(32), I(32))]
        #[on(Arm, 439, I(32), Ptr, I(32), I(32))]
        #[on(Aarch64, 439, I(32), Ptr, I(32), I(32))]
        Faccessat2,
        #[name("fadvise64")]
        #[on(X86, 250, I(32), I(64), UWord, I(32))]
        #[on(X86_64, 221, I(32), I(64), UWord, I(32))]
        #[on(Aarch64, 223, I(32), I(64), I(64), I(32))]
        Fadvise64,
        #[name("fadvise64_64")]
        #[on(X86, 272, I(32), I(64), I(64), I(32))]
        Fadvise64_64,
        #[name("fallocate")]
        #[on(X86, 324, I(32), I(32), I(64), I(64))]
        #[on(X86_64, 285, I(32), I(32), I(64), I(64))]
        #[on(Arm, 352, I(32), I(32), I(64), I(64))]
        #[on(Aarch64, 47, I(32), I(32), I(64), I(64))]
        Fallocate,
        #[name("fanotify_init")]
        #[on(X86, 338, U(32), U(32))]
        #[on(X86_64, 300, U(32), U(32))]
        #[on(Arm, 367, U(32), U(32))]
        #[on(Aarch64, 262, U(32), U(32))]
        FanotifyInit,
        #[name("fanotify_mark")]
        #[on(X86, 339, I(32), U(32), U(64), I(32), Ptr)]
        #[on(X86_64, 301, I(32), U(32), U(64), I(32), Ptr)]
        #[on(Arm, 368, I(32), U(32), U(64), I(32), Ptr)]
        #[on(Aarch64, 263, I(32), U(32), U(64), I(32), Ptr)]
        FanotifyMark,
        #[name("fchdir")]
        #[on(X86, 133, U(32))]
        #[on(X86_64, 81, U(32))]
        #[on(Arm, 133, U(32))]
        #[on(Aarch64, 50, U(32))]
        Fchdir,
        #[name("fchmod")]
        #[on(X86, 94, U(32), U(16))]
        #[on(X86_64, 91, U(32), U(16))]
        #[on(Arm, 94, U(32), U(16))]
        #[on(Aarch64, 52, U(32), U(16))]
        Fchmod,
        #[name("fchmodat")]
        #[on(X86, 306, I(32), Ptr, U(16))]
        #[on(X86_64, 268, I(32), Ptr, U(16))]
        #[on(Arm, 333, I(32), Ptr, U(16))]
        #[on(Aarch64, 53, I(32), Ptr, U(16))]
        Fchmodat,
        #[name("fchmodat2")]
        #[on(X86, 452, I(32), Ptr, U(16), U(32))]
        #[on(X86_64, 452, I(32), Ptr, U(16), U(32))]
        #[on(Arm, 452, I(32), Ptr, U(16), U(32))]
        #[on(Aarch64, 452, I(32), Ptr, U(16), U(32))]
        Fchmodat2,
        #[name("fchown")]
        #[on(X86, 95, U(32), U(16), U(16))]
        #[on(X86_64, 93, U(32), U(32), U(32))]
        #[on(Arm, 95, U(32), U(16), U(16))]
        #[on(Aarch64, 55, U(32), U(32), U(32))]
        Fchown,
        #[name("fchown32")]
        #[on(X86, 207, U(32), U(32), U(32))]
        #[on(Arm, 207, U(32), U(32), U(32))]
        Fchown32,
        #[name("fchownat")]
        #[on(X86, 298, I(32), Ptr, U(32), U(32), I(32))]
        #[on(X86_64, 260, I(32), Ptr, U(32), U(32), I(32))]
        #[on(Arm, 325, I(32), Ptr, U(32), U(32), I(32))]
        #[on(Aarch64, 54, I(32), Ptr, U(32), U(32), I(32))]
        Fchownat,
        #[name("fcntl")]
        #[on(X86, 55, U(32), U(32), UWord)]
        #[on(X86_64, 72, U(32), U(32), UWord)]
        #[on(Arm, 55, U(32), U(32), UWord)]
        #[on(Aarch64, 25, U(32), U(32), UWord)]
        Fcntl,
        #[name("fcntl64")]
        #[on(X86, 221, U(32), U(32), UWord)]
        #[on(Arm, 221, U(32), U(32), UWord)]
        Fcntl64,
        #[name("fdatasync")]
        #[on(X86, 148, U(32))]
        #[on(X86_64, 75, U(32))]
        #[on(Arm, 148, U(32))]
        #[on(Aarch64, 83, U(32))]
        Fdatasync,
        #[name("fgetxattr")]
        #[on(X86, 231, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 193, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 231, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 10, I(32), Ptr, Ptr, UWord)]
        Fgetxattr,
        #[name("file_getattr")]
        #[on(X86, 468, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 468, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 468, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 468, I(32), Ptr, Ptr, UWord, U(32))]
        FileGetattr,
        #[name("file_setattr")]
        #[on(X86, 469, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 469, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 469, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 469, I(32), Ptr, Ptr, UWord, U(32))]
        FileSetattr,
        #[name("finit_module")]
        #[on(X86, 350, I(32), Ptr, I(32))]
        #[on(X86_64, 313, I(32), Ptr, I(32))]
        #[on(Arm, 379, I(32), Ptr, I(32))]
        #[on(Aarch64, 273, I(32), Ptr, I(32))]
        FinitModule,
        #[name("flistxattr")]
        #[on(X86, 234, I(32), Ptr, UWord)]
        #[on(X86_64, 196, I(32), Ptr, UWord)]
        #[on(Arm, 234, I(32), Ptr, UWord)]
        #[on(Aarch64, 13, I(32), Ptr, UWord)]
        Flistxattr,
        #[name("flock")]
        #[on(X86, 143, U(32), U(32))]
        #[on(X86_64, 73, U(32), U(32))]
        #[on(Arm, 143, U(32), U(32))]
        #[on(Aarch64, 32, U(32), U(32))]
        Flock,
        #[name("fork")]
        #[on(X86, 2)]
        #[on(X86_64, 57)]
        #[on(Arm, 2)]
        Fork,
        #[name("fremovexattr")]
        #[on(X86, 237, I(32), Ptr)]
        #[on(X86_64, 199, I(32), Ptr)]
        #[on(Arm, 237, I(32), Ptr)]
        #[on(Aarch64, 16, I(32), Ptr)]
        Fremovexattr,
        #[name("fsconfig")]
        #[on(X86, 431, I(32), U(32), Ptr, Ptr, I(32))]
        #[on(X86_64, 431, I(32), U(32), Ptr, Ptr, I(32))]
        #[on(Arm, 431, I(32), U(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 431, I(32), U(32), Ptr, Ptr, I(32))]
        Fsconfig,
        #[name("fsetxattr")]
        #[on(X86, 228, I(32), Ptr, Ptr, UWord, I(32))]
        #[on(X86_64, 190, I(32), Ptr, Ptr, UWord, I(32))]
        #[on(Arm, 228, I(32), Ptr, Ptr, UWord, I(32))]
        #[on(Aarch64, 7, I(32), Ptr, Ptr, UWord, I(32))]
        Fsetxattr,
        #[name("fsmount")]
        #[on(X86, 432, I(32), U(32), U(32))]
        #[on(X86_64, 432, I(32), U(32), U(32))]
        #[on(Arm, 432, I(32), U(32), U(32))]
        #[on(Aarch64, 432, I(32), U(32), U(32))]
        Fsmount,
        #[name("fsopen")]
        #[on(X86, 430, Ptr, U(32))]
        #[on(X86_64, 430, Ptr, U(32))]
        #[on(Arm, 430, Ptr, U(32))]
        #[on(Aarch64, 430, Ptr, U(32))]
        Fsopen,
        #[name("fspick")]
        #[on(X86, 433, I(32), Ptr, U(32))]
        #[on(X86_64, 433, I(32), Ptr, U(32))]
        #[on(Arm, 433, I(32), Ptr, U(32))]
        #[on(Aarch64, 433, I(32), Ptr, U(32))]
        Fspick,
        #[name("fstat")]
        #[on(X86, 108, U(32), Ptr)]
        #[on(X86_64, 5, U(32), Ptr)]
        #[on(Arm, 108, U(32), Ptr)]
        #[on(Aarch64, 80, U(32), Ptr)]
        Fstat,
        #[name("fstat64")]
        #[on(X86, 197, UWord, Ptr)]
        #[on(Arm, 197, UWord, Ptr)]
        Fstat64,
        #[name("fstatat64")]
        #[on(X86, 300, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 327, I(32), Ptr, Ptr, I(32))]
        Fstatat64,
        #[name("fstatfs")]
        #[on(X86, 100, U(32), Ptr)]
        #[on(X86_64, 138, U(32), Ptr)]
        #[on(Arm, 100, U(32), Ptr)]
        #[on(Aarch64, 44, U(32), Ptr)]
        Fstatfs,
        #[name("fstatfs64")]
        #[on(X86, 269, U(32), UWord, Ptr)]
        #[on(Arm, 267, U(32), UWord, Ptr)]
        Fstatfs64,
        #[name("fsync")]
        #[on(X86, 118, U(32))]
        #[on(X86_64, 74, U(32))]
        #[on(Arm, 118, U(32))]
        #[on(Aarch64, 82, U(32))]
        Fsync,
        #[name("ftime")]
        #[on(X86, 35)]
        Ftime,
        #[name("ftruncate")]
        #[on(X86, 93, U(32), IWord)]
        #[on(X86_64, 77, U(32), IWord)]
        #[on(Arm, 93, U(32), IWord)]
        #[on(Aarch64, 46, U(32), IWord)]
        Ftruncate,
        #[name("ftruncate64")]
        #[on(X86, 194, U(32), I(64))]
        #[on(Arm, 194, U(32), I(64))]
        Ftruncate64,
        #[name("futex")]
        #[on(X86, 240, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        #[on(X86_64, 202, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        #[on(Arm, 240, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        #[on(Aarch64, 98, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        Futex,
        #[name("futex_requeue")]
        #[on(X86, 456, Ptr, U(32), I(32), I(32))]
        #[on(X86_64, 456, Ptr, U(32), I(32), I(32))]
        #[on(Arm, 456, Ptr, U(32), I(32), I(32))]
        #[on(Aarch64, 456, Ptr, U(32), I(32), I(32))]
        FutexRequeue,
        #[name("futex_time64")]
        #[on(X86, 422, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        #[on(Arm, 422, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        FutexTime64,
        #[name("futex_wait")]
        #[on(X86, 455, Ptr, UWord, UWord, U(32), Ptr, I(32))]
        #[on(X86_64, 455, Ptr, UWord, UWord, U(32), Ptr, I(32))]
        #[on(Arm, 455, Ptr, UWord, UWord, U(32), Ptr, I(32))]
        #[on(Aarch64, 455, Ptr, UWord, UWord, U(32), Ptr, I(32))]
        FutexWait,
        #[name("futex_waitv")]
        #[on(X86, 449, Ptr, U(32), U(32), Ptr, I(32))]
        #[on(X86_64, 449, Ptr, U(32), U(32), Ptr, I(32))]
        #[on(Arm, 449, Ptr, U(32), U(32), Ptr, I(32))]
        #[on(Aarch64, 449, Ptr, U(32), U(32), Ptr, I(32))]
        FutexWaitv,
        #[name("futex_wake")]
        #[on(X86, 454, Ptr, UWord, I(32), U(32))]
        #[on(X86_64, 454, Ptr, UWord, I(32), U(32))]
        #[on(Arm, 454, Ptr, UWord, I(32), U(32))]
        #[on(Aarch64, 454, Ptr, UWord, I(32), U(32))]
        FutexWake,
        #[name("futimesat")]
        #[on(X86, 299, U(32), Ptr, Ptr)]
        #[on(X86_64, 261, I(32), Ptr, Ptr)]
        #[on(Arm, 326, U(32), Ptr, Ptr)]
        Futimesat,
        #[name("getcpu")]
        #[on(X86, 318, Ptr, Ptr, Ptr)]
        #[on(X86_64, 309, Ptr, Ptr, Ptr)]
        #[on(Arm, 345, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 168, Ptr, Ptr, Ptr)]
        Getcpu,
        #[name("getcwd")]
        #[on(X86, 183, Ptr, UWord)]
        #[on(X86_64, 79, Ptr, UWord)]
        #[on(Arm, 183, Ptr, UWord)]
        #[on(Aarch64, 17, Ptr, UWord)]
        Getcwd,
        #[name("getdents")]
        #[on(X86, 141, U(32), Ptr, U(32))]
        #[on(X86_64, 78, U(32), Ptr, U(32))]
        #[on(Arm, 141, U(32), Ptr, U(32))]
        Getdents,
        #[name("getdents64")]
        #[on(X86, 220, U(32), Ptr, U(32))]
        #[on(X86_64, 217, U(32), Ptr, U(32))]
        #[on(Arm, 217, U(32), Ptr, U(32))]
        #[on(Aarch64, 61, U(32), Ptr, U(32))]
        Getdents64,
        #[name("getegid")]
        #[on(X86, 50)]
        #[on(X86_64, 108)]
        #[on(Arm, 50)]
        #[on(Aarch64, 177)]
        Getegid,
        #[name("getegid32")]
        #[on(X86, 202)]
        #[on(Arm, 202)]
        Getegid32,
        #[name("geteuid")]
        #[on(X86, 49)]
        #[on(X86_64, 107)]
        #[on(Arm, 49)]
        #[on(Aarch64, 175)]
        Geteuid,
        #[name("geteuid32")]
        #[on(X86, 201)]
        #[on(Arm, 201)]
        Geteuid32,
        #[name("getgid")]
        #[on(X86, 47)]
        #[on(X86_64, 104)]
        #[on(Arm, 47)]
        #[on(Aarch64, 176)]
        Getgid,
        #[name("getgid32")]
        #[on(X86, 200)]
        #[on(Arm, 200)]
        Getgid32,
        #[name("getgroups")]
        #[on(X86, 80, I(32), Ptr)]
        #[on(X86_64, 115, I(32), Ptr)]
        #[on(Arm, 80, I(32), Ptr)]
        #[on(Aarch64, 158, I(32), Ptr)]
        Getgroups,
        #[name("getgroups32")]
        #[on(X86, 205, I(32), Ptr)]
        #[on(Arm, 205, I(32), Ptr)]
        Getgroups32,
        #[name("getitimer")]
        #[on(X86, 105, I(32), Ptr)]
        #[on(X86_64, 36, I(32), Ptr)]
        #[on(Arm, 105, I(32), Ptr)]
        #[on(Aarch64, 102, I(32), Ptr)]
        Getitimer,
        #[name("get_kernel_syms")]
        #[on(X86, 130)]
        #[on(X86_64, 177)]
        GetKernelSyms,
        #[name("get_mempolicy")]
        #[on(X86, 275, Ptr, Ptr, UWord, UWord, UWord)]
        #[on(X86_64, 239, Ptr, Ptr, UWord, UWord, UWord)]
        #[on(Arm, 320, Ptr, Ptr, UWord, UWord, UWord)]
        #[on(Aarch64, 236, Ptr, Ptr, UWord, UWord, UWord)]
        GetMempolicy,
        #[name("getpeername")]
        #[on(X86, 368, I(32), Ptr, Ptr)]
        #[on(X86_64, 52, I(32), Ptr, Ptr)]
        #[on(Arm, 287, I(32), Ptr, Ptr)]
        #[on(Aarch64, 205, I(32), Ptr, Ptr)]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 7)]
        Getpeername,
        #[name("getpgid")]
        #[on(X86, 132, I(32))]
        #[on(X86_64, 121, I(32))]
        #[on(Arm, 132, I(32))]
        #[on(Aarch64, 155, I(32))]
        Getpgid,
        #[name("getpgrp")]
        #[on(X86, 65)]
        #[on(X86_64, 111)]
        #[on(Arm, 65)]
        Getpgrp,
        #[name("getpid")]
        #[on(X86, 20)]
        #[on(X86_64, 39)]
        #[on(Arm, 20)]
        #[on(Aarch64, 172)]
        Getpid,
        #[name("getpmsg")]
        #[on(X86, 188)]
        #[on(X86_64, 181)]
        Getpmsg,
        #[name("getppid")]
        #[on(X86, 64)]
        #[on(X86_64, 110)]
        #[on(Arm, 64)]
        #[on(Aarch64, 173)]
        Getppid,
        #[name("getpriority")]
        #[on(X86, 96, I(32), I(32))]
        #[on(X86_64, 140, I(32), I(32))]
        #[on(Arm, 96, I(32), I(32))]
        #[on(Aarch64, 141, I(32), I(32))]
        Getpriority,
        #[name("getrandom")]
        #[on(X86, 355, Ptr, UWord, U(32))]
        #[on(X86_64, 318, Ptr, UWord, U(32))]
        #[on(Arm, 384, Ptr, UWord, U(32))]
        #[on(Aarch64, 278, Ptr, UWord, U(32))]
        Getrandom,
        #[name("getresgid")]
        #[on(X86, 171, Ptr, Ptr, Ptr)]
        #[on(X86_64, 120, Ptr, Ptr, Ptr)]
        #[on(Arm, 171, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 150, Ptr, Ptr, Ptr)]
        Getresgid,
        #[name("getresgid32")]
        #[on(X86, 211, Ptr, Ptr, Ptr)]
        #[on(Arm, 211, Ptr, Ptr, Ptr)]
        Getresgid32,
        #[name("getresuid")]
        #[on(X86, 165, Ptr, Ptr, Ptr)]
        #[on(X86_64, 118, Ptr, Ptr, Ptr)]
        #[on(Arm, 165, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 148, Ptr, Ptr, Ptr)]
        Getresuid,
        #[name("getresuid32")]
        #[on(X86, 209, Ptr, Ptr, Ptr)]
        #[on(Arm, 209, Ptr, Ptr, Ptr)]
        Getresuid32,
        #[name("getrlimit")]
        #[on(X86, 76, U(32), Ptr)]
        #[on(X86_64, 97, U(32), Ptr)]
        #[on(Aarch64, 163, U(32), Ptr)]
        Getrlimit,
        #[name("get_robust_list")]
        #[on(X86, 312, I(32), Ptr, Ptr)]
        #[on(X86_64, 274, I(32), Ptr, Ptr)]
        #[on(Arm, 339, I(32), Ptr, Ptr)]
        #[on(Aarch64, 100, I(32), Ptr, Ptr)]
        GetRobustList,
        #[name("getrusage")]
        #[on(X86, 77, I(32), Ptr)]
        #[on(X86_64, 98, I(32), Ptr)]
        #[on(Arm, 77, I(32), Ptr)]
        #[on(Aarch64, 165, I(32), Ptr)]
        Getrusage,
        #[name("getsid")]
        #[on(X86, 147, I(32))]
        #[on(X86_64, 124, I(32))]
        #[on(Arm, 147, I(32))]
        #[on(Aarch64, 156, I(32))]
        Getsid,
        #[name("getsockname")]
        #[on(X86, 367, I(32), Ptr, Ptr)]
        #[on(X86_64, 51, I(32), Ptr, Ptr)]
        #[on(Arm, 286, I(32), Ptr, Ptr)]
        #[on(Aarch64, 204, I(32), Ptr, Ptr)]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 6)]
        Getsockname,
        #[name("getsockopt")]
        #[on(X86, 365, I(32), I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 55, I(32), I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 295, I(32), I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 209, I(32), I(32), I(32), Ptr, Ptr)]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 15)]
        Getsockopt,
        #[name("get_thread_area")]
        #[on(X86, 244, Ptr)]
        #[on(X86_64, 211)]
        GetThreadArea,
        #[name("gettid")]
        #[on(X86, 224)]
        #[on(X86_64, 186)]
        #[on(Arm, 224)]
        #[on(Aarch64, 178)]
        Gettid,
        #[name("gettimeofday")]
        #[on(X86, 78, Ptr, Ptr)]
        #[on(X86_64, 96, Ptr, Ptr)]
        #[on(Arm, 78, Ptr, Ptr)]
        #[on(Aarch64, 169, Ptr, Ptr)]
        Gettimeofday,
        #[name("get_tls")]
        #[on(Arm, 983046)]
        GetTls,
        #[name("getuid")]
        #[on(X86, 24)]
        #[on(X86_64, 102)]
        #[on(Arm, 24)]
        #[on(Aarch64, 174)]
        Getuid,
        #[name("getuid32")]
        #[on(X86, 199)]
        #[on(Arm, 199)]
        Getuid32,
        #[name("getxattr")]
        #[on(X86, 229, Ptr, Ptr, Ptr, UWord)]
        #[on(X86_64, 191, Ptr, Ptr, Ptr, UWord)]
        #[on(Arm, 229, Ptr, Ptr, Ptr, UWord)]
        #[on(Aarch64, 8, Ptr, Ptr, Ptr, UWord)]
        Getxattr,
        #[name("getxattrat")]
        #[on(X86, 464, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 464, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Arm, 464, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 464, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        Getxattrat,
        #[name("gtty")]
        #[on(X86, 32)]
        Gtty,
        #[name("idle")]
        #[on(X86, 112)]
        Idle,
        #[name("init_module")]
        #[on(X86, 128, Ptr, UWord, Ptr)]
        #[on(X86_64, 175, Ptr, UWord, Ptr)]
        #[on(Arm, 128, Ptr, UWord, Ptr)]
        #[on(Aarch64, 105, Ptr, UWord, Ptr)]
        InitModule,
        #[name("inotify_add_watch")]
        #[on(X86, 292, I(32), Ptr, U(32))]
        #[on(X86_64, 254, I(32), Ptr, U(32))]
        #[on(Arm, 317, I(32), Ptr, U(32))]
        #[on(Aarch64, 27, I(32), Ptr, U(32))]
        InotifyAddWatch,
        #[name("inotify_init")]
        #[on(X86, 291)]
        #[on(X86_64, 253)]
        #[on(Arm, 316)]
        InotifyInit,
        #[name("inotify_init1")]
        #[on(X86, 332, I(32))]
        #[on(X86_64, 294, I(32))]
        #[on(Arm, 360, I(32))]
        #[on(Aarch64, 26, I(32))]
        InotifyInit1,
        #[name("inotify_rm_watch")]
        #[on(X86, 293, I(32), I(32))]
        #[on(X86_64, 255, I(32), I(32))]
        #[on(Arm, 318, I(32), I(32))]
        #[on(Aarch64, 28, I(32), I(32))]
        InotifyRmWatch,
        #[name("io_cancel")]
        #[on(X86, 249, UWord, Ptr, Ptr)]
        #[on(X86_64, 210, UWord, Ptr, Ptr)]
        #[on(Arm, 247, UWord, Ptr, Ptr)]
        #[on(Aarch64, 3, UWord, Ptr, Ptr)]
        IoCancel,
        #[name("ioctl")]
        #[on(X86, 54, U(32), U(32), UWord)]
        #[on(X86_64, 16, U(32), U(32), UWord)]
        #[on(Arm, 54, U(32), U(32), UWord)]
        #[on(Aarch64, 29, U(32), U(32), UWord)]
        Ioctl,
        #[name("io_destroy")]
        #[on(X86, 246, UWord)]
        #[on(X86_64, 207, UWord)]
        #[on(Arm, 244, UWord)]
        #[on(Aarch64, 1, UWord)]
        IoDestroy,
        #[name("io_getevents")]
        #[on(X86, 247, U(32), I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 208, UWord, IWord, IWord, Ptr, Ptr)]
        #[on(Arm, 245, U(32), I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 4, UWord, IWord, IWord, Ptr, Ptr)]
        IoGetevents,
        #[name("ioperm")]
        #[on(X86, 101, UWord, UWord, I(32))]
        #[on(X86_64, 173, UWord, UWord, I(32))]
        Ioperm,
        #[name("io_pgetevents")]
        #[on(X86, 385, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        #[on(X86_64, 333, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        #[on(Arm, 399, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 292, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        IoPgetevents,
        #[name("io_pgetevents_time64")]
        #[on(X86, 416, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        #[on(Arm, 416, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        IoPgeteventsTime64,
        #[name("iopl")]
        #[on(X86, 110, U(32))]
        #[on(X86_64, 172, U(32))]
        Iopl,
        #[name("ioprio_get")]
        #[on(X86, 290, I(32), I(32))]
        #[on(X86_64, 252, I(32), I(32))]
        #[on(Arm, 315, I(32), I(32))]
        #[on(Aarch64, 31, I(32), I(32))]
        IoprioGet,
        #[name("ioprio_set")]
        #[on(X86, 289, I(32), I(32), I(32))]
        #[on(X86_64, 251, I(32), I(32), I(32))]
        #[on(Arm, 314, I(32), I(32), I(32))]
        #[on(Aarch64, 30, I(32), I(32), I(32))]
        IoprioSet,
        #[name("io_setup")]
        #[on(X86, 245, U(32), Ptr)]
        #[on(X86_64, 206, U(32), Ptr)]
        #[on(Arm, 243, U(32), Ptr)]
        #[on(Aarch64, 0, U(32), Ptr)]
        IoSetup,
        #[name("io_submit")]
        #[on(X86, 248, UWord, IWord, Ptr)]
        #[on(X86_64, 209, UWord, IWord, Ptr)]
        #[on(Arm, 246, UWord, IWord, Ptr)]
        #[on(Aarch64, 2, UWord, IWord, Ptr)]
        IoSubmit,
        #[name("io_uring_enter")]
        #[on(X86, 426, U(32), U(32), U(32), U(32), Ptr, UWord)]
        #[on(X86_64, 426, U(32), U(32), U(32), U(32), Ptr, UWord)]
        #[on(Arm, 426, U(32), U(32), U(32), U(32), Ptr, UWord)]
        #[on(Aarch64, 426, U(32), U(32), U(32), U(32), Ptr, UWord)]
        IoUringEnter,
        #[name("io_uring_register")]
        #[on(X86, 427, U(32), U(32), Ptr, U(32))]
        #[on(X86_64, 427, U(32), U(32), Ptr, U(32))]
        #[on(Arm, 427, U(32), U(32), Ptr, U(32))]
        #[on(Aarch64, 427, U(32), U(32), Ptr, U(32))]
        IoUringRegister,
        #[name("io_uring_setup")]
        #[on(X86, 425, U(32), Ptr)]
        #[on(X86_64, 425, U(32), Ptr)]
        #[on(Arm, 425, U(32), Ptr)]
        #[on(Aarch64, 425, U(32), Ptr)]
        IoUringSetup,
        #[name("ipc")]
        #[on(X86, 117, U(32), I(32), UWord, UWord, Ptr, IWord)]
        Ipc,
        #[name("kcmp")]
        #[on(X86, 349, I(32), I(32), I(32), UWord, UWord)]
        #[on(X86_64, 312, I(32), I(32), I(32), UWord, UWord)]
        #[on(Arm, 378, I(32), I(32), I(32), UWord, UWord)]
        #[on(Aarch64, 272, I(32), I(32), I(32), UWord, UWord)]
        Kcmp,
        #[name("kexec_file_load")]
        #[on(X86_64, 320, I(32), I(32), UWord, Ptr, UWord)]
        #[on(Arm, 401, I(32), I(32), UWord, Ptr, UWord)]
        #[on(Aarch64, 294, I(32), I(32), UWord, Ptr, UWord)]
        KexecFileLoad,
        #[name("kexec_load")]
        #[on(X86, 283, UWord, UWord, Ptr, UWord)]
        #[on(X86_64, 246, UWord, UWord, Ptr, UWord)]
        #[on(Arm, 347, UWord, UWord, Ptr, UWord)]
        #[on(Aarch64, 104, UWord, UWord, Ptr, UWord)]
        KexecLoad,
        #[name("keyctl")]
        #[on(X86, 288, I(32), UWord, UWord, UWord, UWord)]
        #[on(X86_64, 250, I(32), UWord, UWord, UWord, UWord)]
        #[on(Arm, 311, I(32), UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 219, I(32), UWord, UWord, UWord, UWord)]
        Keyctl,
        #[name("kill")]
        #[on(X86, 37, I(32), I(32))]
        #[on(X86_64, 62, I(32), I(32))]
        #[on(Arm, 37, I(32), I(32))]
        #[on(Aarch64, 129, I(32), I(32))]
        Kill,
        #[name("landlock_add_rule")]
        #[on(X86, 445, I(32), U(32), Ptr, U(32))]
        #[on(X86_64, 445, I(32), U(32), Ptr, U(32))]
        #[on(Arm, 445, I(32), U(32), Ptr, U(32))]
        #[on(Aarch64, 445, I(32), U(32), Ptr, U(32))]
        LandlockAddRule,
        #[name("landlock_create_ruleset")]
        #[on(X86, 444, Ptr, UWord, U(32))]
        #[on(X86_64, 444, Ptr, UWord, U(32))]
        #[on(Arm, 444, Ptr, UWord, U(32))]
        #[on(Aarch64, 444, Ptr, UWord, U(32))]
        LandlockCreateRuleset,
        #[name("landlock_restrict_self")]
        #[on(X86, 446, I(32), U(32))]
        #[on(X86_64, 446, I(32), U(32))]
        #[on(Arm, 446, I(32), U(32))]
        #[on(Aarch64, 446, I(32), U(32))]
        LandlockRestrictSelf,
        #[name("lchown")]
        #[on(X86, 16, Ptr, U(16), U(16))]
        #[on(X86_64, 94, Ptr, U(32), U(32))]
        #[on(Arm, 16, Ptr, U(16), U(16))]
        Lchown,
        #[name("lchown32")]
        #[on(X86, 198, Ptr, U(32), U(32))]
        #[on(Arm, 198, Ptr, U(32), U(32))]
        Lchown32,
        #[name("lgetxattr")]
        #[on(X86, 230, Ptr, Ptr, Ptr, UWord)]
        #[on(X86_64, 192, Ptr, Ptr, Ptr, UWord)]
        #[on(Arm, 230, Ptr, Ptr, Ptr, UWord)]
        #[on(Aarch64, 9, Ptr, Ptr, Ptr, UWord)]
        Lgetxattr,
        #[name("link")]
        #[on(X86, 9, Ptr, Ptr)]
        #[on(X86_64, 86, Ptr, Ptr)]
        #[on(Arm, 9, Ptr, Ptr)]
        Link,
        #[name("linkat")]
        #[on(X86, 303, I(32), Ptr, I(32), Ptr, I(32))]
        #[on(X86_64, 265, I(32), Ptr, I(32), Ptr, I(32))]
        #[on(Arm, 330, I(32), Ptr, I(32), Ptr, I(32))]
        #[on(Aarch64, 37, I(32), Ptr, I(32), Ptr, I(32))]
        Linkat,
        #[name("listen")]
        #[on(X86, 363, I(32), I(32))]
        #[on(X86_64, 50, I(32), I(32))]
        #[on(Arm, 284, I(32), I(32))]
        #[on(Aarch64, 201, I(32), I(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 4)]
        Listen,
        #[name("listmount")]
        #[on(X86, 458, Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 458, Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 458, Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 458, Ptr, Ptr, UWord, U(32))]
        Listmount,
        #[name("listns")]
        #[on(X86, 470, Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 470, Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 470, Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 470, Ptr, Ptr, UWord, U(32))]
        Listns,
        #[name("listxattr")]
        #[on(X86, 232, Ptr, Ptr, UWord)]
        #[on(X86_64, 194, Ptr, Ptr, UWord)]
        #[on(Arm, 232, Ptr, Ptr, UWord)]
        #[on(Aarch64, 11, Ptr, Ptr, UWord)]
        Listxattr,
        #[name("listxattrat")]
        #[on(X86, 465, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(X86_64, 465, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Arm, 465, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Aarch64, 465, I(32), Ptr, U(32), Ptr, UWord)]
        Listxattrat,
        #[name("llistxattr")]
        #[on(X86, 233, Ptr, Ptr, UWord)]
        #[on(X86_64, 195, Ptr, Ptr, UWord)]
        #[on(Arm, 233, Ptr, Ptr, UWord)]
        #[on(Aarch64, 12, Ptr, Ptr, UWord)]
        Llistxattr,
        #[name("_llseek")]
        #[on(X86, 140, U(32), UWord, UWord, Ptr, U(32))]
        #[on(Arm, 140, U(32), UWord, UWord, Ptr, U(32))]
        _Llseek,
        #[name("lock")]
        #[on(X86, 53)]
        Lock,
        #[name("lookup_dcookie")]
        #[on(X86, 253)]
        #[on(X86_64, 212)]
        #[on(Arm, 249)]
        #[on(Aarch64, 18)]
        LookupDcookie,
        #[name("lremovexattr")]
        #[on(X86, 236, Ptr, Ptr)]
        #[on(X86_64, 198, Ptr, Ptr)]
        #[on(Arm, 236, Ptr, Ptr)]
        #[on(Aarch64, 15, Ptr, Ptr)]
        Lremovexattr,
        #[name("lseek")]
        #[on(X86, 19, U(32), IWord, U(32))]
        #[on(X86_64, 8, U(32), IWord, U(32))]
        #[on(Arm, 19, U(32), IWord, U(32))]
        #[on(Aarch64, 62, U(32), IWord, U(32))]
        Lseek,
        #[name("lsetxattr")]
        #[on(X86, 227, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(X86_64, 189, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Arm, 227, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Aarch64, 6, Ptr, Ptr, Ptr, UWord, I(32))]
        Lsetxattr,
        #[name("lsm_get_self_attr")]
        #[on(X86, 459, U(32), Ptr, Ptr, U(32))]
        #[on(X86_64, 459, U(32), Ptr, Ptr, U(32))]
        #[on(Arm, 459, U(32), Ptr, Ptr, U(32))]
        #[on(Aarch64, 459, U(32), Ptr, Ptr, U(32))]
        LsmGetSelfAttr,
        #[name("lsm_list_modules")]
        #[on(X86, 461, Ptr, Ptr, U(32))]
        #[on(X86_64, 461, Ptr, Ptr, U(32))]
        #[on(Arm, 461, Ptr, Ptr, U(32))]
        #[on(Aarch64, 461, Ptr, Ptr, U(32))]
        LsmListModules,
        #[name("lsm_set_self_attr")]
        #[on(X86, 460, U(32), Ptr, U(32), U(32))]
        #[on(X86_64, 460, U(32), Ptr, U(32), U(32))]
        #[on(Arm, 460, U(32), Ptr, U(32), U(32))]
        #[on(Aarch64, 460, U(32), Ptr, U(32), U(32))]
        LsmSetSelfAttr,
        #[name("lstat")]
        #[on(X86, 107, Ptr, Ptr)]
        #[on(X86_64, 6, Ptr, Ptr)]
        #[on(Arm, 107, Ptr, Ptr)]
        Lstat,
        #[name("lstat64")]
        #[on(X86, 196, Ptr, Ptr)]
        #[on(Arm, 196, Ptr, Ptr)]
        Lstat64,
        #[name("madvise")]
        #[on(X86, 219, UWord, UWord, I(32))]
        #[on(X86_64, 28, UWord, UWord, I(32))]
        #[on(Arm, 220, UWord, UWord, I(32))]
        #[on(Aarch64, 233, UWord, UWord, I(32))]
        Madvise,
        #[name("map_shadow_stack")]
        #[on(X86, 453, UWord, UWord, U(32))]
        #[on(X86_64, 453, UWord, UWord, U(32))]
        #[on(Arm, 453, UWord, UWord, U(32))]
        #[on(Aarch64, 453, UWord, UWord, U(32))]
        MapShadowStack,
        #[name("mbind")]
        #[on(X86, 274, UWord, UWord, UWord, Ptr, UWord, U(32))]
        #[on(X86_64, 237, UWord, UWord, UWord, Ptr, UWord, U(32))]
        #[on(Arm, 319, UWord, UWord, UWord, Ptr, UWord, U(32))]
        #[on(Aarch64, 235, UWord, UWord, UWord, Ptr, UWord, U(32))]
        Mbind,
        #[name("membarrier")]
        #[on(X86, 375, I(32), U(32), I(32))]
        #[on(X86_64, 324, I(32), U(32), I(32))]
        #[on(Arm, 389, I(32), U(32), I(32))]
        #[on(Aarch64, 283, I(32), U(32), I(32))]
        Membarrier,
        #[name("memfd_create")]
        #[on(X86, 356, Ptr, U(32))]
        #[on(X86_64, 319, Ptr, U(32))]
        #[on(Arm, 385, Ptr, U(32))]
        #[on(Aarch64, 279, Ptr, U(32))]
        MemfdCreate,
        #[name("memfd_secret")]
        #[on(X86, 447, U(32))]
        #[on(X86_64, 447, U(32))]
        #[on(Aarch64, 447, U(32))]
        MemfdSecret,
        #[name("migrate_pages")]
        #[on(X86, 294, I(32), UWord, Ptr, Ptr)]
        #[on(X86_64, 256, I(32), UWord, Ptr, Ptr)]
        #[on(Arm, 400, I(32), UWord, Ptr, Ptr)]
        #[on(Aarch64, 238, I(32), UWord, Ptr, Ptr)]
        MigratePages,
        #[name("mincore")]
        #[on(X86, 218, UWord, UWord, Ptr)]
        #[on(X86_64, 27, UWord, UWord, Ptr)]
        #[on(Arm, 219, UWord, UWord, Ptr)]
        #[on(Aarch64, 232, UWord, UWord, Ptr)]
        Mincore,
        #[name("mkdir")]
        #[on(X86, 39, Ptr, U(16))]
        #[on(X86_64, 83, Ptr, U(16))]
        #[on(Arm, 39, Ptr, U(16))]
        Mkdir,
        #[name("mkdirat")]
        #[on(X86, 296, I(32), Ptr, U(16))]
        #[on(X86_64, 258, I(32), Ptr, U(16))]
        #[on(Arm, 323, I(32), Ptr, U(16))]
        #[on(Aarch64, 34, I(32), Ptr, U(16))]
        Mkdirat,
        #[name("mknod")]
        #[on(X86, 14, Ptr, U(16), U(32))]
        #[on(X86_64, 133, Ptr, U(16), U(32))]
        #[on(Arm, 14, Ptr, U(16), U(32))]
        Mknod,
        #[name("mknodat")]
        #[on(X86, 297, I(32), Ptr, U(16), U(32))]
        #[on(X86_64, 259, I(32), Ptr, U(16), U(32))]
        #[on(Arm, 324, I(32), Ptr, U(16), U(32))]
        #[on(Aarch64, 33, I(32), Ptr, U(16), U(32))]
        Mknodat,
        #[name("mlock")]
        #[on(X86, 150, UWord, UWord)]
        #[on(X86_64, 149, UWord, UWord)]
        #[on(Arm, 150, UWord, UWord)]
        #[on(Aarch64, 228, UWord, UWord)]
        Mlock,
        #[name("mlock2")]
        #[on(X86, 376, UWord, UWord, I(32))]
        #[on(X86_64, 325, UWord, UWord, I(32))]
        #[on(Arm, 390, UWord, UWord, I(32))]
        #[on(Aarch64, 284, UWord, UWord, I(32))]
        Mlock2,
        #[name("mlockall")]
        #[on(X86, 152, I(32))]
        #[on(X86_64, 151, I(32))]
        #[on(Arm, 152, I(32))]
        #[on(Aarch64, 230, I(32))]
        Mlockall,
        #[name("mmap")]
        #[on(X86, 90, Ptr)]
        #[on(X86_64, 9, UWord, UWord, UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 222, UWord, UWord, UWord, UWord, UWord, UWord)]
        Mmap,
        #[name("mmap2")]
        #[on(X86, 192, UWord, UWord, UWord, UWord, UWord, UWord)]
        #[on(Arm, 192, UWord, UWord, UWord, UWord, UWord, UWord)]
        Mmap2,
        #[name("modify_ldt")]
        #[on(X86, 123, I(32), Ptr, UWord)]
        #[on(X86_64, 154, I(32), Ptr, UWord)]
        ModifyLdt,
        #[name("mount")]
        #[on(X86, 21, Ptr, Ptr, Ptr, UWord, Ptr)]
        #[on(X86_64, 165, Ptr, Ptr, Ptr, UWord, Ptr)]
        #[on(Arm, 21, Ptr, Ptr, Ptr, UWord, Ptr)]
        #[on(Aarch64, 40, Ptr, Ptr, Ptr, UWord, Ptr)]
        Mount,
        #[name("mount_setattr")]
        #[on(X86, 442, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(X86_64, 442, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Arm, 442, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Aarch64, 442, I(32), Ptr, U(32), Ptr, UWord)]
        MountSetattr,
        #[name("move_mount")]
        #[on(X86, 429, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(X86_64, 429, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(Arm, 429, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(Aarch64, 429, I(32), Ptr, I(32), Ptr, U(32))]
        MoveMount,
        #[name("move_pages")]
        #[on(X86, 317, I(32), UWord, Ptr, Ptr, Ptr, I(32))]
        #[on(X86_64, 279, I(32), UWord, Ptr, Ptr, Ptr, I(32))]
        #[on(Arm, 344, I(32), UWord, Ptr, Ptr, Ptr, I(32))]
        #[on(Aarch64, 239, I(32), UWord, Ptr, Ptr, Ptr, I(32))]
        MovePages,
        #[name("mprotect")]
        #[on(X86, 125, UWord, UWord, UWord)]
        #[on(X86_64, 10, UWord, UWord, UWord)]
        #[on(Arm, 125, UWord, UWord, UWord)]
        #[on(Aarch64, 226, UWord, UWord, UWord)]
        Mprotect,
        #[name("mpx")]
        #[on(X86, 56)]
        Mpx,
        #[name("mq_getsetattr")]
        #[on(X86, 282, I(32), Ptr, Ptr)]
        #[on(X86_64, 245, I(32), Ptr, Ptr)]
        #[on(Arm, 279, I(32), Ptr, Ptr)]
        #[on(Aarch64, 185, I(32), Ptr, Ptr)]
        MqGetsetattr,
        #[name("mq_notify")]
        #[on(X86, 281, I(32), Ptr)]
        #[on(X86_64, 244, I(32), Ptr)]
        #[on(Arm, 278, I(32), Ptr)]
        #[on(Aarch64, 184, I(32), Ptr)]
        MqNotify,
        #[name("mq_open")]
        #[on(X86, 277, Ptr, I(32), U(16), Ptr)]
        #[on(X86_64, 240, Ptr, I(32), U(16), Ptr)]
        #[on(Arm, 274, Ptr, I(32), U(16), Ptr)]
        #[on(Aarch64, 180, Ptr, I(32), U(16), Ptr)]
        MqOpen,
        #[name("mq_timedreceive")]
        #[on(X86, 280, I(32), Ptr, U(32), Ptr, Ptr)]
        #[on(X86_64, 243, I(32), Ptr, UWord, Ptr, Ptr)]
        #[on(Arm, 277, I(32), Ptr, U(32), Ptr, Ptr)]
        #[on(Aarch64, 183, I(32), Ptr, UWord, Ptr, Ptr)]
        MqTimedreceive,
        #[name("mq_timedreceive_time64")]
        #[on(X86, 419, I(32), Ptr, UWord, Ptr, Ptr)]
        #[on(Arm, 419, I(32), Ptr, UWord, Ptr, Ptr)]
        MqTimedreceiveTime64,
        #[name("mq_timedsend")]
        #[on(X86, 279, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(X86_64, 242, I(32), Ptr, UWord, U(32), Ptr)]
        #[on(Arm, 276, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Aarch64, 182, I(32), Ptr, UWord, U(32), Ptr)]
        MqTimedsend,
        #[name("mq_timedsend_time64")]
        #[on(X86, 418, I(32), Ptr, UWord, U(32), Ptr)]
        #[on(Arm, 418, I(32), Ptr, UWord, U(32), Ptr)]
        MqTimedsendTime64,
        #[name("mq_unlink")]
        #[on(X86, 278, Ptr)]
        #[on(X86_64, 241, Ptr)]
        #[on(Arm, 275, Ptr)]
        #[on(Aarch64, 181, Ptr)]
        MqUnlink,
        #[name("mremap")]
        #[on(X86, 163, UWord, UWord, UWord, UWord, UWord)]
        #[on(X86_64, 25, UWord, UWord, UWord, UWord, UWord)]
        #[on(Arm, 163, UWord, UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 216, UWord, UWord, UWord, UWord, UWord)]
        Mremap,
        #[name("mseal")]
        #[on(X86, 462, UWord, UWord, UWord)]
        #[on(X86_64, 462, UWord, UWord, UWord)]
        #[on(Arm, 462, UWord, UWord, UWord)]
        #[on(Aarch64, 462, UWord, UWord, UWord)]
        Mseal,
        #[name("msgctl")]
        #[on(X86, 402, I(32), I(32), Ptr)]
        #[on(X86_64, 71, I(32), I(32), Ptr)]
        #[on(Arm, 304, I(32), I(32), Ptr)]
        #[on(Aarch64, 187, I(32), I(32), Ptr)]
        #[mux(X86, Ipc, @0 & 0xFFFF == 14)]
        Msgctl,
        #[name("msgget")]
        #[on(X86, 399, I(32), I(32))]
        #[on(X86_64, 68, I(32), I(32))]
        #[on(Arm, 303, I(32), I(32))]
        #[on(Aarch64, 186, I(32), I(32))]
        #[mux(X86, Ipc, @0 & 0xFFFF == 13)]
        Msgget,
        #[name("msgrcv")]
        #[on(X86, 401, I(32), Ptr, UWord, IWord, I(32))]
        #[on(X86_64, 70, I(32), Ptr, UWord, IWord, I(32))]
        #[on(Arm, 302, I(32), Ptr, UWord, IWord, I(32))]
        #[on(Aarch64, 188, I(32), Ptr, UWord, IWord, I(32))]
        #[mux(X86, Ipc, @0 & 0xFFFF == 12)]
        Msgrcv,
        #[name("msgsnd")]
        #[on(X86, 400, I(32), Ptr, UWord, I(32))]
        #[on(X86_64, 69, I(32), Ptr, UWord, I(32))]
        #[on(Arm, 301, I(32), Ptr, UWord, I(32))]
        #[on(Aarch64, 189, I(32), Ptr, UWord, I(32))]
        #[mux(X86, Ipc, @0 & 0xFFFF == 11)]
        Msgsnd,
        #[name("msync")]
        #[on(X86, 144, UWord, UWord, I(32))]
        #[on(X86_64, 26, UWord, UWord, I(32))]
        #[on(Arm, 144, UWord, UWord, I(32))]
        #[on(Aarch64, 227, UWord, UWord, I(32))]
        Msync,
        #[name("munlock")]
        #[on(X86, 151, UWord, UWord)]
        #[on(X86_64, 150, UWord, UWord)]
        #[on(Arm, 151, UWord, UWord)]
        #[on(Aarch64, 229, UWord, UWord)]
        Munlock,
        #[name("munlockall")]
        #[on(X86, 153)]
        #[on(X86_64, 152)]
        #[on(Arm, 153)]
        #[on(Aarch64, 231)]
        Munlockall,
        #[name("munmap")]
        #[on(X86, 91, UWord, UWord)]
        #[on(X86_64, 11, UWord, UWord)]
        #[on(Arm, 91, UWord, UWord)]
        #[on(Aarch64, 215, UWord, UWord)]
        Munmap,
        #[name("name_to_handle_at")]
        #[on(X86, 341, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(X86_64, 303, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(Arm, 370, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(Aarch64, 264, I(32), Ptr, Ptr, Ptr, I(32))]
        NameToHandleAt,
        #[name("nanosleep")]
        #[on(X86, 162, Ptr, Ptr)]
        #[on(X86_64, 35, Ptr, Ptr)]
        #[on(Arm, 162, Ptr, Ptr)]
        #[on(Aarch64, 101, Ptr, Ptr)]
        Nanosleep,
        #[name("newfstatat")]
        #[on(X86_64, 262, I(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 79, I(32), Ptr, Ptr, I(32))]
        Newfstatat,
        #[name("_newselect")]
        #[on(X86, 142, I(32), Ptr, Ptr, Ptr, Ptr)]
        #[on(Arm, 142, I(32), Ptr, Ptr, Ptr, Ptr)]
        _Newselect,
        #[name("nfsservctl")]
        #[on(X86, 169)]
        #[on(X86_64, 180)]
        #[on(Arm, 169)]
        #[on(Aarch64, 42)]
        Nfsservctl,
        #[name("nice")]
        #[on(X86, 34, I(32))]
        #[on(Arm, 34, I(32))]
        Nice,
        #[name("oldfstat")]
        #[on(X86, 28, U(32), Ptr)]
        Oldfstat,
        #[name("oldlstat")]
        #[on(X86, 84, Ptr, Ptr)]
        Oldlstat,
        #[name("oldolduname")]
        #[on(X86, 59, Ptr)]
        Oldolduname,
        #[name("oldstat")]
        #[on(X86, 18, Ptr, Ptr)]
        Oldstat,
        #[name("olduname")]
        #[on(X86, 109, Ptr)]
        Olduname,
        #[name("open")]
        #[on(X86, 5, Ptr, I(32), U(16))]
        #[on(X86_64, 2, Ptr, I(32), U(16))]
        #[on(Arm, 5, Ptr, I(32), U(16))]
        Open,
        #[name("openat")]
        #[on(X86, 295, I(32), Ptr, I(32), U(16))]
        #[on(X86_64, 257, I(32), Ptr, I(32), U(16))]
        #[on(Arm, 322, I(32), Ptr, I(32), U(16))]
        #[on(Aarch64, 56, I(32), Ptr, I(32), U(16))]
        Openat,
        #[name("openat2")]
        #[on(X86, 437, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 437, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 437, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 437, I(32), Ptr, Ptr, UWord)]
        Openat2,
        #[name("open_by_handle_at")]
        #[on(X86, 342, I(32), Ptr, I(32))]
        #[on(X86_64, 304, I(32), Ptr, I(32))]
        #[on(Arm, 371, I(32), Ptr, I(32))]
        #[on(Aarch64, 265, I(32), Ptr, I(32))]
        OpenByHandleAt,
        #[name("open_tree")]
        #[on(X86, 428, I(32), Ptr, U(32))]
        #[on(X86_64, 428, I(32), Ptr, U(32))]
        #[on(Arm, 428, I(32), Ptr, U(32))]
        #[on(Aarch64, 428, I(32), Ptr, U(32))]
        OpenTree,
        #[name("open_tree_attr")]
        #[on(X86, 467, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(X86_64, 467, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Arm, 467, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Aarch64, 467, I(32), Ptr, U(32), Ptr, UWord)]
        OpenTreeAttr,
        #[name("pause")]
        #[on(X86, 29)]
        #[on(X86_64, 34)]
        #[on(Arm, 29)]
        Pause,
        #[name("pciconfig_iobase")]
        #[on(Arm, 271, IWord, UWord, UWord)]
        PciconfigIobase,
        #[name("pciconfig_read")]
        #[on(Arm, 272, UWord, UWord, UWord, UWord, Ptr)]
        PciconfigRead,
        #[name("pciconfig_write")]
        #[on(Arm, 273, UWord, UWord, UWord, UWord, Ptr)]
        PciconfigWrite,
        #[name("perf_event_open")]
        #[on(X86, 336, Ptr, I(32), I(32), I(32), UWord)]
        #[on(X86_64, 298, Ptr, I(32), I(32), I(32), UWord)]
        #[on(Arm, 364, Ptr, I(32), I(32), I(32), UWord)]
        #[on(Aarch64, 241, Ptr, I(32), I(32), I(32), UWord)]
        PerfEventOpen,
        #[name("personality")]
        #[on(X86, 136, U(32))]
        #[on(X86_64, 135, U(32))]
        #[on(Arm, 136, U(32))]
        #[on(Aarch64, 92, U(32))]
        Personality,
        #[name("pidfd_getfd")]
        #[on(X86, 438, I(32), I(32), U(32))]
        #[on(X86_64, 438, I(32), I(32), U(32))]
        #[on(Arm, 438, I(32), I(32), U(32))]
        #[on(Aarch64, 438, I(32), I(32), U(32))]
        PidfdGetfd,
        #[name("pidfd_open")]
        #[on(X86, 434, I(32), U(32))]
        #[on(X86_64, 434, I(32), U(32))]
        #[on(Arm, 434, I(32), U(32))]
        #[on(Aarch64, 434, I(32), U(32))]
        PidfdOpen,
        #[name("pidfd_send_signal")]
        #[on(X86, 424, I(32), I(32), Ptr, U(32))]
        #[on(X86_64, 424, I(32), I(32), Ptr, U(32))]
        #[on(Arm, 424, I(32), I(32), Ptr, U(32))]
        #[on(Aarch64, 424, I(32), I(32), Ptr, U(32))]
        PidfdSendSignal,
        #[name("pipe")]
        #[on(X86, 42, Ptr)]
        #[on(X86_64, 22, Ptr)]
        #[on(Arm, 42, Ptr)]
        Pipe,
        #[name("pipe2")]
        #[on(X86, 331, Ptr, I(32))]
        #[on(X86_64, 293, Ptr, I(32))]
        #[on(Arm, 359, Ptr, I(32))]
        #[on(Aarch64, 59, Ptr, I(32))]
        Pipe2,
        #[name("pivot_root")]
        #[on(X86, 217, Ptr, Ptr)]
        #[on(X86_64, 155, Ptr, Ptr)]
        #[on(Arm, 218, Ptr, Ptr)]
        #[on(Aarch64, 41, Ptr, Ptr)]
        PivotRoot,
        #[name("pkey_alloc")]
        #[on(X86, 381, UWord, UWord)]
        #[on(X86_64, 330, UWord, UWord)]
        #[on(Arm, 395, UWord, UWord)]
        #[on(Aarch64, 289, UWord, UWord)]
        PkeyAlloc,
        #[name("pkey_free")]
        #[on(X86, 382, I(32))]
        #[on(X86_64, 331, I(32))]
        #[on(Arm, 396, I(32))]
        #[on(Aarch64, 290, I(32))]
        PkeyFree,
        #[name("pkey_mprotect")]
        #[on(X86, 380, UWord, UWord, UWord, I(32))]
        #[on(X86_64, 329, UWord, UWord, UWord, I(32))]
        #[on(Arm, 394, UWord, UWord, UWord, I(32))]
        #[on(Aarch64, 288, UWord, UWord, UWord, I(32))]
        PkeyMprotect,
        #[name("poll")]
        #[on(X86, 168, Ptr, U(32), I(32))]
        #[on(X86_64, 7, Ptr, U(32), I(32))]
        #[on(Arm, 168, Ptr, U(32), I(32))]
        Poll,
        #[name("ppoll")]
        #[on(X86, 309, Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 271, Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Arm, 336, Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 73, Ptr, U(32), Ptr, Ptr, UWord)]
        Ppoll,
        #[name("ppoll_time64")]
        #[on(X86, 414, Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Arm, 414, Ptr, U(32), Ptr, Ptr, UWord)]
        PpollTime64,
        #[name("prctl")]
        #[on(X86, 172, I(32), UWord, UWord, UWord, UWord)]
        #[on(X86_64, 157, I(32), UWord, UWord, UWord, UWord)]
        #[on(Arm, 172, I(32), UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 167, I(32), UWord, UWord, UWord, UWord)]
        Prctl,
        #[name("pread64")]
        #[on(X86, 180, U(32), Ptr, UWord, I(64))]
        #[on(X86_64, 17, U(32), Ptr, UWord, I(64))]
        #[on(Arm, 180, U(32), Ptr, UWord, I(64))]
        #[on(Aarch64, 67, U(32), Ptr, UWord, I(64))]
        Pread64,
        #[name("preadv")]
        #[on(X86, 333, UWord, Ptr, UWord, UWord, UWord)]
        #[on(X86_64, 295, UWord, Ptr, UWord, UWord, UWord)]
        #[on(Arm, 361, UWord, Ptr, UWord, UWord, UWord)]
        #[on(Aarch64, 69, UWord, Ptr, UWord, UWord, UWord)]
        Preadv,
        #[name("preadv2")]
        #[on(X86, 378, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(X86_64, 327, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(Arm, 392, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(Aarch64, 286, UWord, Ptr, UWord, UWord, UWord, I(32))]
        Preadv2,
        #[name("prlimit64")]
        #[on(X86, 340, I(32), U(32), Ptr, Ptr)]
        #[on(X86_64, 302, I(32), U(32), Ptr, Ptr)]
        #[on(Arm, 369, I(32), U(32), Ptr, Ptr)]
        #[on(Aarch64, 261, I(32), U(32), Ptr, Ptr)]
        Prlimit64,
        #[name("process_madvise")]
        #[on(X86, 440, I(32), Ptr, UWord, I(32), U(32))]
        #[on(X86_64, 440, I(32), Ptr, UWord, I(32), U(32))]
        #[on(Arm, 440, I(32), Ptr, UWord, I(32), U(32))]
        #[on(Aarch64, 440, I(32), Ptr, UWord, I(32), U(32))]
        ProcessMadvise,
        #[name("process_mrelease")]
        #[on(X86, 448, I(32), U(32))]
        #[on(X86_64, 448, I(32), U(32))]
        #[on(Arm, 448, I(32), U(32))]
        #[on(Aarch64, 448, I(32), U(32))]
        ProcessMrelease,
        #[name("process_vm_readv")]
        #[on(X86, 347, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(X86_64, 310, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(Arm, 376, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(Aarch64, 270, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        ProcessVmReadv,
        #[name("process_vm_writev")]
        #[on(X86, 348, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(X86_64, 311, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(Arm, 377, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(Aarch64, 271, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        ProcessVmWritev,
        #[name("prof")]
        #[on(X86, 44)]
        Prof,
        #[name("profil")]
        #[on(X86, 98)]
        Profil,
        #[name("pselect6")]
        #[on(X86, 308, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        #[on(X86_64, 270, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        #[on(Arm, 335, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 72, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        Pselect6,
        #[name("pselect6_time64")]
        #[on(X86, 413, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        #[on(Arm, 413, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        Pselect6Time64,
        #[name("ptrace")]
        #[on(X86, 26, IWord, IWord, UWord, UWord)]
        #[on(X86_64, 101, IWord, IWord, UWord, UWord)]
        #[on(Arm, 26, IWord, IWord, UWord, UWord)]
        #[on(Aarch64, 117, IWord, IWord, UWord, UWord)]
        Ptrace,
        #[name("putpmsg")]
        #[on(X86, 189)]
        #[on(X86_64, 182)]
        Putpmsg,
        #[name("pwrite64")]
        #[on(X86, 181, U(32), Ptr, UWord, I(64))]
        #[on(X86_64, 18, U(32), Ptr, UWord, I(64))]
        #[on(Arm, 181, U(32), Ptr, UWord, I(64))]
        #[on(Aarch64, 68, U(32), Ptr, UWord, I(64))]
        Pwrite64,
        #[name("pwritev")]
        #[on(X86, 334, UWord, Ptr, UWord, UWord, UWord)]
        #[on(X86_64, 296, UWord, Ptr, UWord, UWord, UWord)]
        #[on(Arm, 362, UWord, Ptr, UWord, UWord, UWord)]
        #[on(Aarch64, 70, UWord, Ptr, UWord, UWord, UWord)]
        Pwritev,
        #[name("pwritev2")]
        #[on(X86, 379, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(X86_64, 328, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(Arm, 393, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(Aarch64, 287, UWord, Ptr, UWord, UWord, UWord, I(32))]
        Pwritev2,
        #[name("query_module")]
        #[on(X86, 167)]
        #[on(X86_64, 178)]
        QueryModule,
        #[name("quotactl")]
        #[on(X86, 131, U(32), Ptr, U(32), Ptr)]
        #[on(X86_64, 179, U(32), Ptr, U(32), Ptr)]
        #[on(Arm, 131, U(32), Ptr, U(32), Ptr)]
        #[on(Aarch64, 60, U(32), Ptr, U(32), Ptr)]
        Quotactl,
        #[name("quotactl_fd")]
        #[on(X86, 443, U(32), U(32), U(32), Ptr)]
        #[on(X86_64, 443, U(32), U(32), U(32), Ptr)]
        #[on(Arm, 443, U(32), U(32), U(32), Ptr)]
        #[on(Aarch64, 443, U(32), U(32), U(32), Ptr)]
        QuotactlFd,
        #[name("read")]
        #[on(X86, 3, U(32), Ptr, UWord)]
        #[on(X86_64, 0, U(32), Ptr, UWord)]
        #[on(Arm, 3, U(32), Ptr, UWord)]
        #[on(Aarch64, 63, U(32), Ptr, UWord)]
        Read,
        #[name("readahead")]
        #[on(X86, 225, I(32), I(64), UWord)]
        #[on(X86_64, 187, I(32), I(64), UWord)]
        #[on(Arm, 225, I(32), I(64), UWord)]
        #[on(Aarch64, 213, I(32), I(64), UWord)]
        Readahead,
        #[name("readdir")]
        #[on(X86, 89, U(32), Ptr, U(32))]
        Readdir,
        #[name("readlink")]
        #[on(X86, 85, Ptr, Ptr, I(32))]
        #[on(X86_64, 89, Ptr, Ptr, I(32))]
        #[on(Arm, 85, Ptr, Ptr, I(32))]
        Readlink,
        #[name("readlinkat")]
        #[on(X86, 305, I(32), Ptr, Ptr, I(32))]
        #[on(X86_64, 267, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 332, I(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 78, I(32), Ptr, Ptr, I(32))]
        Readlinkat,
        #[name("readv")]
        #[on(X86, 145, UWord, Ptr, UWord)]
        #[on(X86_64, 19, UWord, Ptr, UWord)]
        #[on(Arm, 145, UWord, Ptr, UWord)]
        #[on(Aarch64, 65, UWord, Ptr, UWord)]
        Readv,
        #[name("reboot")]
        #[on(X86, 88, I(32), I(32), U(32), Ptr)]
        #[on(X86_64, 169, I(32), I(32), U(32), Ptr)]
        #[on(Arm, 88, I(32), I(32), U(32), Ptr)]
        #[on(Aarch64, 142, I(32), I(32), U(32), Ptr)]
        Reboot,
        #[name("recv")]
        #[on(Arm, 291, I(32), Ptr, UWord, U(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 10)]
        Recv,
        #[name("recvfrom")]
        #[on(X86, 371, I(32), Ptr, UWord, U(32), Ptr, Ptr)]
        #[on(X86_64, 45, I(32), Ptr, UWord, U(32), Ptr, Ptr)]
        #[on(Arm, 292, I(32), Ptr, UWord, U(32), Ptr, Ptr)]
        #[on(Aarch64, 207, I(32), Ptr, UWord, U(32), Ptr, Ptr)]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 12)]
        Recvfrom,
        #[name("recvmmsg")]
        #[on(X86, 337, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(X86_64, 299, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Arm, 365, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Aarch64, 243, I(32), Ptr, U(32), U(32), Ptr)]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 19)]
        Recvmmsg,
        #[name("recvmmsg_time64")]
        #[on(X86, 417, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Arm, 417, I(32), Ptr, U(32), U(32), Ptr)]
        RecvmmsgTime64,
        #[name("recvmsg")]
        #[on(X86, 372, I(32), Ptr, U(32))]
        #[on(X86_64, 47, I(32), Ptr, U(32))]
        #[on(Arm, 297, I(32), Ptr, U(32))]
        #[on(Aarch64, 212, I(32), Ptr, U(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 17)]
        Recvmsg,
        #[name("remap_file_pages")]
        #[on(X86, 257, UWord, UWord, UWord, UWord, UWord)]
        #[on(X86_64, 216, UWord, UWord, UWord, UWord, UWord)]
        #[on(Arm, 253, UWord, UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 234, UWord, UWord, UWord, UWord, UWord)]
        RemapFilePages,
        #[name("removexattr")]
        #[on(X86, 235, Ptr, Ptr)]
        #[on(X86_64, 197, Ptr, Ptr)]
        #[on(Arm, 235, Ptr, Ptr)]
        #[on(Aarch64, 14, Ptr, Ptr)]
        Removexattr,
        #[name("removexattrat")]
        #[on(X86, 466, I(32), Ptr, U(32), Ptr)]
        #[on(X86_64, 466, I(32), Ptr, U(32), Ptr)]
        #[on(Arm, 466, I(32), Ptr, U(32), Ptr)]
        #[on(Aarch64, 466, I(32), Ptr, U(32), Ptr)]
        Removexattrat,
        #[name("rename")]
        #[on(X86, 38, Ptr, Ptr)]
        #[on(X86_64, 82, Ptr, Ptr)]
        #[on(Arm, 38, Ptr, Ptr)]
        Rename,
        #[name("renameat")]
        #[on(X86, 302, I(32), Ptr, I(32), Ptr)]
        #[on(X86_64, 264, I(32), Ptr, I(32), Ptr)]
        #[on(Arm, 329, I(32), Ptr, I(32), Ptr)]
        #[on(Aarch64, 38, I(32), Ptr, I(32), Ptr)]
        Renameat,
        #[name("renameat2")]
        #[on(X86, 353, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(X86_64, 316, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(Arm, 382, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(Aarch64, 276, I(32), Ptr, I(32), Ptr, U(32))]
        Renameat2,
        #[name("request_key")]
        #[on(X86, 287, Ptr, Ptr, Ptr, I(32))]
        #[on(X86_64, 249, Ptr, Ptr, Ptr, I(32))]
        #[on(Arm, 310, Ptr, Ptr, Ptr, I(32))]
        #[on(Aarch64, 218, Ptr, Ptr, Ptr, I(32))]
        RequestKey,
        #[name("restart_syscall")]
        #[on(X86, 0)]
        #[on(X86_64, 219)]
        #[on(Arm, 0)]
        #[on(Aarch64, 128)]
        RestartSyscall,
        #[name("rmdir")]
        #[on(X86, 40, Ptr)]
        #[on(X86_64, 84, Ptr)]
        #[on(Arm, 40, Ptr)]
        Rmdir,
        #[name("rseq")]
        #[on(X86, 386, Ptr, U(32), I(32), U(32))]
        #[on(X86_64, 334, Ptr, U(32), I(32), U(32))]
        #[on(Arm, 398, Ptr, U(32), I(32), U(32))]
        #[on(Aarch64, 293, Ptr, U(32), I(32), U(32))]
        Rseq,
        #[name("rseq_slice_yield")]
        #[on(X86, 471)]
        #[on(X86_64, 471)]
        #[on(Arm, 471)]
        #[on(Aarch64, 471)]
        RseqSliceYield,
        #[name("rt_sigaction")]
        #[on(X86, 174, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 13, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 174, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 134, I(32), Ptr, Ptr, UWord)]
        RtSigaction,
        #[name("rt_sigpending")]
        #[on(X86, 176, Ptr, UWord)]
        #[on(X86_64, 127, Ptr, UWord)]
        #[on(Arm, 176, Ptr, UWord)]
        #[on(Aarch64, 136, Ptr, UWord)]
        RtSigpending,
        #[name("rt_sigprocmask")]
        #[on(X86, 175, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 14, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 175, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 135, I(32), Ptr, Ptr, UWord)]
        RtSigprocmask,
        #[name("rt_sigqueueinfo")]
        #[on(X86, 178, I(32), I(32), Ptr)]
        #[on(X86_64, 129, I(32), I(32), Ptr)]
        #[on(Arm, 178, I(32), I(32), Ptr)]
        #[on(Aarch64, 138, I(32), I(32), Ptr)]
        RtSigqueueinfo,
        #[name("rt_sigreturn")]
        #[on(X86, 173)]
        #[on(X86_64, 15)]
        #[on(Arm, 173)]
        #[on(Aarch64, 139)]
        RtSigreturn,
        #[name("rt_sigsuspend")]
        #[on(X86, 179, Ptr, UWord)]
        #[on(X86_64, 130, Ptr, UWord)]
        #[on(Arm, 179, Ptr, UWord)]
        #[on(Aarch64, 133, Ptr, UWord)]
        RtSigsuspend,
        #[name("rt_sigtimedwait")]
        #[on(X86, 177, Ptr, Ptr, Ptr, UWord)]
        #[on(X86_64, 128, Ptr, Ptr, Ptr, UWord)]
        #[on(Arm, 177, Ptr, Ptr, Ptr, UWord)]
        #[on(Aarch64, 137, Ptr, Ptr, Ptr, UWord)]
        RtSigtimedwait,
        #[name("rt_sigtimedwait_time64")]
        #[on(X86, 421, Ptr, Ptr, Ptr, UWord)]
        #[on(Arm, 421, Ptr, Ptr, Ptr, UWord)]
        RtSigtimedwaitTime64,
        #[name("rt_tgsigqueueinfo")]
        #[on(X86, 335, I(32), I(32), I(32), Ptr)]
        #[on(X86_64, 297, I(32), I(32), I(32), Ptr)]
        #[on(Arm, 363, I(32), I(32), I(32), Ptr)]
        #[on(Aarch64, 240, I(32), I(32), I(32), Ptr)]
        RtTgsigqueueinfo,
        #[name("sched_getaffinity")]
        #[on(X86, 242, I(32), U(32), Ptr)]
        #[on(X86_64, 204, I(32), U(32), Ptr)]
        #[on(Arm, 242, I(32), U(32), Ptr)]
        #[on(Aarch64, 123, I(32), U(32), Ptr)]
        SchedGetaffinity,
        #[name("sched_getattr")]
        #[on(X86, 352, I(32), Ptr, U(32), U(32))]
        #[on(X86_64, 315, I(32), Ptr, U(32), U(32))]
        #[on(Arm, 381, I(32), Ptr, U(32), U(32))]
        #[on(Aarch64, 275, I(32), Ptr, U(32), U(32))]
        SchedGetattr,
        #[name("sched_getparam")]
        #[on(X86, 155, I(32), Ptr)]
        #[on(X86_64, 143, I(32), Ptr)]
        #[on(Arm, 155, I(32), Ptr)]
        #[on(Aarch64, 121, I(32), Ptr)]
        SchedGetparam,
        #[name("sched_get_priority_max")]
        #[on(X86, 159, I(32))]
        #[on(X86_64, 146, I(32))]
        #[on(Arm, 159, I(32))]
        #[on(Aarch64, 125, I(32))]
        SchedGetPriorityMax,
        #[name("sched_get_priority_min")]
        #[on(X86, 160, I(32))]
        #[on(X86_64, 147, I(32))]
        #[on(Arm, 160, I(32))]
        #[on(Aarch64, 126, I(32))]
        SchedGetPriorityMin,
        #[name("sched_getscheduler")]
        #[on(X86, 157, I(32))]
        #[on(X86_64, 145, I(32))]
        #[on(Arm, 157, I(32))]
        #[on(Aarch64, 120, I(32))]
        SchedGetscheduler,
        #[name("sched_rr_get_interval")]
        #[on(X86, 161, I(32), Ptr)]
        #[on(X86_64, 148, I(32), Ptr)]
        #[on(Arm, 161, I(32), Ptr)]
        #[on(Aarch64, 127, I(32), Ptr)]
        SchedRrGetInterval,
        #[name("sched_rr_get_interval_time64")]
        #[on(X86, 423, I(32), Ptr)]
        #[on(Arm, 423, I(32), Ptr)]
        SchedRrGetIntervalTime64,
        #[name("sched_setaffinity")]
        #[on(X86, 241, I(32), U(32), Ptr)]
        #[on(X86_64, 203, I(32), U(32), Ptr)]
        #[on(Arm, 241, I(32), U(32), Ptr)]
        #[on(Aarch64, 122, I(32), U(32), Ptr)]
        SchedSetaffinity,
        #[name("sched_setattr")]
        #[on(X86, 351, I(32), Ptr, U(32))]
        #[on(X86_64, 314, I(32), Ptr, U(32))]
        #[on(Arm, 380, I(32), Ptr, U(32))]
        #[on(Aarch64, 274, I(32), Ptr, U(32))]
        SchedSetattr,
        #[name("sched_setparam")]
        #[on(X86, 154, I(32), Ptr)]
        #[on(X86_64, 142, I(32), Ptr)]
        #[on(Arm, 154, I(32), Ptr)]
        #[on(Aarch64, 118, I(32), Ptr)]
        SchedSetparam,
        #[name("sched_setscheduler")]
        #[on(X86, 156, I(32), I(32), Ptr)]
        #[on(X86_64, 144, I(32), I(32), Ptr)]
        #[on(Arm, 156, I(32), I(32), Ptr)]
        #[on(Aarch64, 119, I(32), I(32), Ptr)]
        SchedSetscheduler,
        #[name("sched_yield")]
        #[on(X86, 158)]
        #[on(X86_64, 24)]
        #[on(Arm, 158)]
        #[on(Aarch64, 124)]
        SchedYield,
        #[name("seccomp")]
        #[on(X86, 354, U(32), U(32), Ptr)]
        #[on(X86_64, 317, U(32), U(32), Ptr)]
        #[on(Arm, 383, U(32), U(32), Ptr)]
        #[on(Aarch64, 277, U(32), U(32), Ptr)]
        Seccomp,
        #[name("security")]
        #[on(X86_64, 185)]
        Security,
        #[name("select")]
        #[on(X86, 82, Ptr)]
        #[on(X86_64, 23, I(32), Ptr, Ptr, Ptr, Ptr)]
        Select,
        #[name("semctl")]
        #[on(X86, 394, I(32), I(32), I(32), UWord)]
        #[on(X86_64, 66, I(32), I(32), I(32), UWord)]
        #[on(Arm, 300, I(32), I(32), I(32), UWord)]
        #[on(Aarch64, 191, I(32), I(32), I(32), UWord)]
        #[mux(X86, Ipc, @0 & 0xFFFF == 3)]
        Semctl,
        #[name("semget")]
        #[on(X86, 393, I(32), I(32), I(32))]
        #[on(X86_64, 64, I(32), I(32), I(32))]
        #[on(Arm, 299, I(32), I(32), I(32))]
        #[on(Aarch64, 190, I(32), I(32), I(32))]
        #[mux(X86, Ipc, @0 & 0xFFFF == 2)]
        Semget,
        #[name("semop")]
        #[on(X86_64, 65, I(32), Ptr, U(32))]
        #[on(Arm, 298, I(32), Ptr, U(32))]
        #[on(Aarch64, 193, I(32), Ptr, U(32))]
        #[mux(X86, Ipc, @0 & 0xFFFF == 1)]
        Semop,
        #[name("semtimedop")]
        #[on(X86_64, 220, I(32), Ptr, U(32), Ptr)]
        #[on(Arm, 312, I(32), Ptr, U(32), Ptr)]
        #[on(Aarch64, 192, I(32), Ptr, U(32), Ptr)]
        #[mux(X86, Ipc, @0 & 0xFFFF == 4)]
        Semtimedop,
        #[name("semtimedop_time64")]
        #[on(X86, 420, I(32), Ptr, U(32), Ptr)]
        #[on(Arm, 420, I(32), Ptr, U(32), Ptr)]
        SemtimedopTime64,
        #[name("send")]
        #[on(Arm, 289, I(32), Ptr, UWord, U(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 9)]
        Send,
        #[name("sendfile")]
        #[on(X86, 187, I(32), I(32), Ptr, UWord)]
        #[on(X86_64, 40, I(32), I(32), Ptr, UWord)]
        #[on(Arm, 187, I(32), I(32), Ptr, UWord)]
        #[on(Aarch64, 71, I(32), I(32), Ptr, UWord)]
        Sendfile,
        #[name("sendfile64")]
        #[on(X86, 239, I(32), I(32), Ptr, UWord)]
        #[on(Arm, 239, I(32), I(32), Ptr, UWord)]
        Sendfile64,
        #[name("sendmmsg")]
        #[on(X86, 345, I(32), Ptr, U(32), U(32))]
        #[on(X86_64, 307, I(32), Ptr, U(32), U(32))]
        #[on(Arm, 374, I(32), Ptr, U(32), U(32))]
        #[on(Aarch64, 269, I(32), Ptr, U(32), U(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 20)]
        Sendmmsg,
        #[name("sendmsg")]
        #[on(X86, 370, I(32), Ptr, U(32))]
        #[on(X86_64, 46, I(32), Ptr, U(32))]
        #[on(Arm, 296, I(32), Ptr, U(32))]
        #[on(Aarch64, 211, I(32), Ptr, U(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 16)]
        Sendmsg,
        #[name("sendto")]
        #[on(X86, 369, I(32), Ptr, UWord, U(32), Ptr, I(32))]
        #[on(X86_64, 44, I(32), Ptr, UWord, U(32), Ptr, I(32))]
        #[on(Arm, 290, I(32), Ptr, UWord, U(32), Ptr, I(32))]
        #[on(Aarch64, 206, I(32), Ptr, UWord, U(32), Ptr, I(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 11)]
        Sendto,
        #[name("setdomainname")]
        #[on(X86, 121, Ptr, I(32))]
        #[on(X86_64, 171, Ptr, I(32))]
        #[on(Arm, 121, Ptr, I(32))]
        #[on(Aarch64, 162, Ptr, I(32))]
        Setdomainname,
        #[name("setfsgid")]
        #[on(X86, 139, U(16))]
        #[on(X86_64, 123, U(32))]
        #[on(Arm, 139, U(16))]
        #[on(Aarch64, 152, U(32))]
        Setfsgid,
        #[name("setfsgid32")]
        #[on(X86, 216, U(32))]
        #[on(Arm, 216, U(32))]
        Setfsgid32,
        #[name("setfsuid")]
        #[on(X86, 138, U(16))]
        #[on(X86_64, 122, U(32))]
        #[on(Arm, 138, U(16))]
        #[on(Aarch64, 151, U(32))]
        Setfsuid,
        #[name("setfsuid32")]
        #[on(X86, 215, U(32))]
        #[on(Arm, 215, U(32))]
        Setfsuid32,
        #[name("setgid")]
        #[on(X86, 46, U(16))]
        #[on(X86_64, 106, U(32))]
        #[on(Arm, 46, U(16))]
        #[on(Aarch64, 144, U(32))]
        Setgid,
        #[name("setgid32")]
        #[on(X86, 214, U(32))]
        #[on(Arm, 214, U(32))]
        Setgid32,
        #[name("setgroups")]
        #[on(X86, 81, I(32), Ptr)]
        #[on(X86_64, 116, I(32), Ptr)]
        #[on(Arm, 81, I(32), Ptr)]
        #[on(Aarch64, 159, I(32), Ptr)]
        Setgroups,
        #[name("setgroups32")]
        #[on(X86, 206, I(32), Ptr)]
        #[on(Arm, 206, I(32), Ptr)]
        Setgroups32,
        #[name("sethostname")]
        #[on(X86, 74, Ptr, I(32))]
        #[on(X86_64, 170, Ptr, I(32))]
        #[on(Arm, 74, Ptr, I(32))]
        #[on(Aarch64, 161, Ptr, I(32))]
        Sethostname,
        #[name("setitimer")]
        #[on(X86, 104, I(32), Ptr, Ptr)]
        #[on(X86_64, 38, I(32), Ptr, Ptr)]
        #[on(Arm, 104, I(32), Ptr, Ptr)]
        #[on(Aarch64, 103, I(32), Ptr, Ptr)]
        Setitimer,
        #[name("set_mempolicy")]
        #[on(X86, 276, I(32), Ptr, UWord)]
        #[on(X86_64, 238, I(32), Ptr, UWord)]
        #[on(Arm, 321, I(32), Ptr, UWord)]
        #[on(Aarch64, 237, I(32), Ptr, UWord)]
        SetMempolicy,
        #[name("set_mempolicy_home_node")]
        #[on(X86, 450, UWord, UWord, UWord, UWord)]
        #[on(X86_64, 450, UWord, UWord, UWord, UWord)]
        #[on(Arm, 450, UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 450, UWord, UWord, UWord, UWord)]
        SetMempolicyHomeNode,
        #[name("setns")]
        #[on(X86, 346, I(32), I(32))]
        #[on(X86_64, 308, I(32), I(32))]
        #[on(Arm, 375, I(32), I(32))]
        #[on(Aarch64, 268, I(32), I(32))]
        Setns,
        #[name("setpgid")]
        #[on(X86, 57, I(32), I(32))]
        #[on(X86_64, 109, I(32), I(32))]
        #[on(Arm, 57, I(32), I(32))]
        #[on(Aarch64, 154, I(32), I(32))]
        Setpgid,
        #[name("setpriority")]
        #[on(X86, 97, I(32), I(32), I(32))]
        #[on(X86_64, 141, I(32), I(32), I(32))]
        #[on(Arm, 97, I(32), I(32), I(32))]
        #[on(Aarch64, 140, I(32), I(32), I(32))]
        Setpriority,
        #[name("setregid")]
        #[on(X86, 71, U(16), U(16))]
        #[on(X86_64, 114, U(32), U(32))]
        #[on(Arm, 71, U(16), U(16))]
        #[on(Aarch64, 143, U(32), U(32))]
        Setregid,
        #[name("setregid32")]
        #[on(X86, 204, U(32), U(32))]
        #[on(Arm, 204, U(32), U(32))]
        Setregid32,
        #[name("setresgid")]
        #[on(X86, 170, U(16), U(16), U(16))]
        #[on(X86_64, 119, U(32), U(32), U(32))]
        #[on(Arm, 170, U(16), U(16), U(16))]
        #[on(Aarch64, 149, U(32), U(32), U(32))]
        Setresgid,
        #[name("setresgid32")]
        #[on(X86, 210, U(32), U(32), U(32))]
        #[on(Arm, 210, U(32), U(32), U(32))]
        Setresgid32,
        #[name("setresuid")]
        #[on(X86, 164, U(16), U(16), U(16))]
        #[on(X86_64, 117, U(32), U(32), U(32))]
        #[on(Arm, 164, U(16), U(16), U(16))]
        #[on(Aarch64, 147, U(32), U(32), U(32))]
        Setresuid,
        #[name("setresuid32")]
        #[on(X86, 208, U(32), U(32), U(32))]
        #[on(Arm, 208, U(32), U(32), U(32))]
        Setresuid32,
        #[name("setreuid")]
        #[on(X86, 70, U(16), U(16))]
        #[on(X86_64, 113, U(32), U(32))]
        #[on(Arm, 70, U(16), U(16))]
        #[on(Aarch64, 145, U(32), U(32))]
        Setreuid,
        #[name("setreuid32")]
        #[on(X86, 203, U(32), U(32))]
        #[on(Arm, 203, U(32), U(32))]
        Setreuid32,
        #[name("setrlimit")]
        #[on(X86, 75, U(32), Ptr)]
        #[on(X86_64, 160, U(32), Ptr)]
        #[on(Arm, 75, U(32), Ptr)]
        #[on(Aarch64, 164, U(32), Ptr)]
        Setrlimit,
        #[name("set_robust_list")]
        #[on(X86, 311, Ptr, UWord)]
        #[on(X86_64, 273, Ptr, UWord)]
        #[on(Arm, 338, Ptr, UWord)]
        #[on(Aarch64, 99, Ptr, UWord)]
        SetRobustList,
        #[name("setsid")]
        #[on(X86, 66)]
        #[on(X86_64, 112)]
        #[on(Arm, 66)]
        #[on(Aarch64, 157)]
        Setsid,
        #[name("setsockopt")]
        #[on(X86, 366, I(32), I(32), I(32), Ptr, I(32))]
        #[on(X86_64, 54, I(32), I(32), I(32), Ptr, I(32))]
        #[on(Arm, 294, I(32), I(32), I(32), Ptr, I(32))]
        #[on(Aarch64, 208, I(32), I(32), I(32), Ptr, I(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 14)]
        Setsockopt,
        #[name("set_thread_area")]
        #[on(X86, 243, Ptr)]
        #[on(X86_64, 205)]
        SetThreadArea,
        #[name("set_tid_address")]
        #[on(X86, 258, Ptr)]
        #[on(X86_64, 218, Ptr)]
        #[on(Arm, 256, Ptr)]
        #[on(Aarch64, 96, Ptr)]
        SetTidAddress,
        #[name("settimeofday")]
        #[on(X86, 79, Ptr, Ptr)]
        #[on(X86_64, 164, Ptr, Ptr)]
        #[on(Arm, 79, Ptr, Ptr)]
        #[on(Aarch64, 170, Ptr, Ptr)]
        Settimeofday,
        #[name("set_tls")]
        #[on(Arm, 983045, UWord)]
        SetTls,
        #[name("setuid")]
        #[on(X86, 23, U(16))]
        #[on(X86_64, 105, U(32))]
        #[on(Arm, 23, U(16))]
        #[on(Aarch64, 146, U(32))]
        Setuid,
        #[name("setuid32")]
        #[on(X86, 213, U(32))]
        #[on(Arm, 213, U(32))]
        Setuid32,
        #[name("setxattr")]
        #[on(X86, 226, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(X86_64, 188, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Arm, 226, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Aarch64, 5, Ptr, Ptr, Ptr, UWord, I(32))]
        Setxattr,
        #[name("setxattrat")]
        #[on(X86, 463, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 463, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Arm, 463, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 463, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        Setxattrat,
        #[name("sgetmask")]
        #[on(X86, 68)]
        Sgetmask,
        #[name("shmat")]
        #[on(X86, 397, I(32), Ptr, I(32))]
        #[on(X86_64, 30, I(32), Ptr, I(32))]
        #[on(Arm, 305, I(32), Ptr, I(32))]
        #[on(Aarch64, 196, I(32), Ptr, I(32))]
        #[mux(X86, Ipc, @0 & 0xFFFF == 21)]
        Shmat,
        #[name("shmctl")]
        #[on(X86, 396, I(32), I(32), Ptr)]
        #[on(X86_64, 31, I(32), I(32), Ptr)]
        #[on(Arm, 308, I(32), I(32), Ptr)]
        #[on(Aarch64, 195, I(32), I(32), Ptr)]
        #[mux(X86, Ipc, @0 & 0xFFFF == 24)]
        Shmctl,
        #[name("shmdt")]
        #[on(X86, 398, Ptr)]
        #[on(X86_64, 67, Ptr)]
        #[on(Arm, 306, Ptr)]
        #[on(Aarch64, 197, Ptr)]
        #[mux(X86, Ipc, @0 & 0xFFFF == 22)]
        Shmdt,
        #[name("shmget")]
        #[on(X86, 395, I(32), UWord, I(32))]
        #[on(X86_64, 29, I(32), UWord, I(32))]
        #[on(Arm, 307, I(32), UWord, I(32))]
        #[on(Aarch64, 194, I(32), UWord, I(32))]
        #[mux(X86, Ipc, @0 & 0xFFFF == 23)]
        Shmget,
        #[name("shutdown")]
        #[on(X86, 373, I(32), I(32))]
        #[on(X86_64, 48, I(32), I(32))]
        #[on(Arm, 293, I(32), I(32))]
        #[on(Aarch64, 210, I(32), I(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 13)]
        Shutdown,
        #[name("sigaction")]
        #[on(X86, 67, I(32), Ptr, Ptr)]
        #[on(Arm, 67, I(32), Ptr, Ptr)]
        Sigaction,
        #[name("sigaltstack")]
        #[on(X86, 186, Ptr, Ptr)]
        #[on(X86_64, 131, Ptr, Ptr)]
        #[on(Arm, 186, Ptr, Ptr)]
        #[on(Aarch64, 132, Ptr, Ptr)]
        Sigaltstack,
        #[name("signal")]
        #[on(X86, 48, I(32), Ptr)]
        Signal,
        #[name("signalfd")]
        #[on(X86, 321, I(32), Ptr, UWord)]
        #[on(X86_64, 282, I(32), Ptr, UWord)]
        #[on(Arm, 349, I(32), Ptr, UWord)]
        Signalfd,
        #[name("signalfd4")]
        #[on(X86, 327, I(32), Ptr, UWord, I(32))]
        #[on(X86_64, 289, I(32), Ptr, UWord, I(32))]
        #[on(Arm, 355, I(32), Ptr, UWord, I(32))]
        #[on(Aarch64, 74, I(32), Ptr, UWord, I(32))]
        Signalfd4,
        #[name("sigpending")]
        #[on(X86, 73, Ptr)]
        #[on(Arm, 73, Ptr)]
        Sigpending,
        #[name("sigprocmask")]
        #[on(X86, 126, I(32), Ptr, Ptr)]
        #[on(Arm, 126, I(32), Ptr, Ptr)]
        Sigprocmask,
        #[name("sigreturn")]
        #[on(X86, 119)]
        #[on(Arm, 119)]
        Sigreturn,
        #[name("sigsuspend")]
        #[on(X86, 72, I(32), I(32), UWord)]
        #[on(Arm, 72, I(32), I(32), UWord)]
        Sigsuspend,
        #[name("socket")]
        #[on(X86, 359, I(32), I(32), I(32))]
        #[on(X86_64, 41, I(32), I(32), I(32))]
        #[on(Arm, 281, I(32), I(32), I(32))]
        #[on(Aarch64, 198, I(32), I(32), I(32))]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 1)]
        Socket,
        #[name("socketcall")]
        #[on(X86, 102, I(32), Ptr)]
        Socketcall,
        #[name("socketpair")]
        #[on(X86, 360, I(32), I(32), I(32), Ptr)]
        #[on(X86_64, 53, I(32), I(32), I(32), Ptr)]
        #[on(Arm, 288, I(32), I(32), I(32), Ptr)]
        #[on(Aarch64, 199, I(32), I(32), I(32), Ptr)]
        #[mux(X86, Socketcall, @0 & 0xFFFF_FFFF == 8)]
        Socketpair,
        #[name("splice")]
        #[on(X86, 313, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(X86_64, 275, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(Arm, 340, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(Aarch64, 76, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        Splice,
        #[name("ssetmask")]
        #[on(X86, 69, I(32))]
        Ssetmask,
        #[name("stat")]
        #[on(X86, 106, Ptr, Ptr)]
        #[on(X86_64, 4, Ptr, Ptr)]
        #[on(Arm, 106, Ptr, Ptr)]
        Stat,
        #[name("stat64")]
        #[on(X86, 195, Ptr, Ptr)]
        #[on(Arm, 195, Ptr, Ptr)]
        Stat64,
        #[name("statfs")]
        #[on(X86, 99, Ptr, Ptr)]
        #[on(X86_64, 137, Ptr, Ptr)]
        #[on(Arm, 99, Ptr, Ptr)]
        #[on(Aarch64, 43, Ptr, Ptr)]
        Statfs,
        #[name("statfs64")]
        #[on(X86, 268, Ptr, UWord, Ptr)]
        #[on(Arm, 266, Ptr, UWord, Ptr)]
        Statfs64,
        #[name("statmount")]
        #[on(X86, 457, Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 457, Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 457, Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 457, Ptr, Ptr, UWord, U(32))]
        Statmount,
        #[name("statx")]
        #[on(X86, 383, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(X86_64, 332, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Arm, 397, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Aarch64, 291, I(32), Ptr, U(32), U(32), Ptr)]
        Statx,
        #[name("stime")]
        #[on(X86, 25, Ptr)]
        Stime,
        #[name("stty")]
        #[on(X86, 31)]
        Stty,
        #[name("swapoff")]
        #[on(X86, 115, Ptr)]
        #[on(X86_64, 168, Ptr)]
        #[on(Arm, 115, Ptr)]
        #[on(Aarch64, 225, Ptr)]
        Swapoff,
        #[name("swapon")]
        #[on(X86, 87, Ptr, I(32))]
        #[on(X86_64, 167, Ptr, I(32))]
        #[on(Arm, 87, Ptr, I(32))]
        #[on(Aarch64, 224, Ptr, I(32))]
        Swapon,
        #[name("symlink")]
        #[on(X86, 83, Ptr, Ptr)]
        #[on(X86_64, 88, Ptr, Ptr)]
        #[on(Arm, 83, Ptr, Ptr)]
        Symlink,
        #[name("symlinkat")]
        #[on(X86, 304, Ptr, I(32), Ptr)]
        #[on(X86_64, 266, Ptr, I(32), Ptr)]
        #[on(Arm, 331, Ptr, I(32), Ptr)]
        #[on(Aarch64, 36, Ptr, I(32), Ptr)]
        Symlinkat,
        #[name("sync")]
        #[on(X86, 36)]
        #[on(X86_64, 162)]
        #[on(Arm, 36)]
        #[on(Aarch64, 81)]
        Sync,
        #[name("sync_file_range")]
        #[on(X86, 314, I(32), I(64), I(64), U(32))]
        #[on(X86_64, 277, I(32), I(64), I(64), U(32))]
        #[on(Aarch64, 84, I(32), I(64), I(64), U(32))]
        SyncFileRange,
        #[name("syncfs")]
        #[on(X86, 344, I(32))]
        #[on(X86_64, 306, I(32))]
        #[on(Arm, 373, I(32))]
        #[on(Aarch64, 267, I(32))]
        Syncfs,
        #[name("_sysctl")]
        #[on(X86, 149)]
        #[on(X86_64, 156)]
        #[on(Arm, 149)]
        _Sysctl,
        #[name("sysfs")]
        #[on(X86, 135, I(32), UWord, UWord)]
        #[on(X86_64, 139, I(32), UWord, UWord)]
        #[on(Arm, 135, I(32), UWord, UWord)]
        Sysfs,
        #[name("sysinfo")]
        #[on(X86, 116, Ptr)]
        #[on(X86_64, 99, Ptr)]
        #[on(Arm, 116, Ptr)]
        #[on(Aarch64, 179, Ptr)]
        Sysinfo,
        #[name("syslog")]
        #[on(X86, 103, I(32), Ptr, I(32))]
        #[on(X86_64, 103, I(32), Ptr, I(32))]
        #[on(Arm, 103, I(32), Ptr, I(32))]
        #[on(Aarch64, 116, I(32), Ptr, I(32))]
        Syslog,
        #[name("tee")]
        #[on(X86, 315, I(32), I(32), UWord, U(32))]
        #[on(X86_64, 276, I(32), I(32), UWord, U(32))]
        #[on(Arm, 342, I(32), I(32), UWord, U(32))]
        #[on(Aarch64, 77, I(32), I(32), UWord, U(32))]
        Tee,
        #[name("tgkill")]
        #[on(X86, 270, I(32), I(32), I(32))]
        #[on(X86_64, 234, I(32), I(32), I(32))]
        #[on(Arm, 268, I(32), I(32), I(32))]
        #[on(Aarch64, 131, I(32), I(32), I(32))]
        Tgkill,
        #[name("time")]
        #[on(X86, 13, Ptr)]
        #[on(X86_64, 201, Ptr)]
        Time,
        #[name("timer_create")]
        #[on(X86, 259, I(32), Ptr, Ptr)]
        #[on(X86_64, 222, I(32), Ptr, Ptr)]
        #[on(Arm, 257, I(32), Ptr, Ptr)]
        #[on(Aarch64, 107, I(32), Ptr, Ptr)]
        TimerCreate,
        #[name("timer_delete")]
        #[on(X86, 263, I(32))]
        #[on(X86_64, 226, I(32))]
        #[on(Arm, 261, I(32))]
        #[on(Aarch64, 111, I(32))]
        TimerDelete,
        #[name("timerfd_create")]
        #[on(X86, 322, I(32), I(32))]
        #[on(X86_64, 283, I(32), I(32))]
        #[on(Arm, 350, I(32), I(32))]
        #[on(Aarch64, 85, I(32), I(32))]
        TimerfdCreate,
        #[name("timerfd_gettime")]
        #[on(X86, 326, I(32), Ptr)]
        #[on(X86_64, 287, I(32), Ptr)]
        #[on(Arm, 354, I(32), Ptr)]
        #[on(Aarch64, 87, I(32), Ptr)]
        TimerfdGettime,
        #[name("timerfd_gettime64")]
        #[on(X86, 410, I(32), Ptr)]
        #[on(Arm, 410, I(32), Ptr)]
        TimerfdGettime64,
        #[name("timerfd_settime")]
        #[on(X86, 325, I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 286, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 353, I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 86, I(32), I(32), Ptr, Ptr)]
        TimerfdSettime,
        #[name("timerfd_settime64")]
        #[on(X86, 411, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 411, I(32), I(32), Ptr, Ptr)]
        TimerfdSettime64,
        #[name("timer_getoverrun")]
        #[on(X86, 262, I(32))]
        #[on(X86_64, 225, I(32))]
        #[on(Arm, 260, I(32))]
        #[on(Aarch64, 109, I(32))]
        TimerGetoverrun,
        #[name("timer_gettime")]
        #[on(X86, 261, I(32), Ptr)]
        #[on(X86_64, 224, I(32), Ptr)]
        #[on(Arm, 259, I(32), Ptr)]
        #[on(Aarch64, 108, I(32), Ptr)]
        TimerGettime,
        #[name("timer_gettime64")]
        #[on(X86, 408, I(32), Ptr)]
        #[on(Arm, 408, I(32), Ptr)]
        TimerGettime64,
        #[name("timer_settime")]
        #[on(X86, 260, I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 223, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 258, I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 110, I(32), I(32), Ptr, Ptr)]
        TimerSettime,
        #[name("timer_settime64")]
        #[on(X86, 409, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 409, I(32), I(32), Ptr, Ptr)]
        TimerSettime64,
        #[name("times")]
        #[on(X86, 43, Ptr)]
        #[on(X86_64, 100, Ptr)]
        #[on(Arm, 43, Ptr)]
        #[on(Aarch64, 153, Ptr)]
        Times,
        #[name("tkill")]
        #[on(X86, 238, I(32), I(32))]
        #[on(X86_64, 200, I(32), I(32))]
        #[on(Arm, 238, I(32), I(32))]
        #[on(Aarch64, 130, I(32), I(32))]
        Tkill,
        #[name("truncate")]
        #[on(X86, 92, Ptr, IWord)]
        #[on(X86_64, 76, Ptr, IWord)]
        #[on(Arm, 92, Ptr, IWord)]
        #[on(Aarch64, 45, Ptr, IWord)]
        Truncate,
        #[name("truncate64")]
        #[on(X86, 193, Ptr, I(64))]
        #[on(Arm, 193, Ptr, I(64))]
        Truncate64,
        #[name("tuxcall")]
        #[on(X86_64, 184)]
        Tuxcall,
        #[name("ugetrlimit")]
        #[on(X86, 191, U(32), Ptr)]
        #[on(Arm, 191, U(32), Ptr)]
        Ugetrlimit,
        #[name("ulimit")]
        #[on(X86, 58)]
        Ulimit,
        #[name("umask")]
        #[on(X86, 60, I(32))]
        #[on(X86_64, 95, I(32))]
        #[on(Arm, 60, I(32))]
        #[on(Aarch64, 166, I(32))]
        Umask,
        #[name("umount")]
        #[on(X86, 22, Ptr)]
        Umount,
        #[name("umount2")]
        #[on(X86, 52, Ptr, I(32))]
        #[on(X86_64, 166, Ptr, I(32))]
        #[on(Arm, 52, Ptr, I(32))]
        #[on(Aarch64, 39, Ptr, I(32))]
        Umount2,
        #[name("uname")]
        #[on(X86, 122, Ptr)]
        #[on(X86_64, 63, Ptr)]
        #[on(Arm, 122, Ptr)]
        #[on(Aarch64, 160, Ptr)]
        Uname,
        #[name("unlink")]
        #[on(X86, 10, Ptr)]
        #[on(X86_64, 87, Ptr)]
        #[on(Arm, 10, Ptr)]
        Unlink,
        #[name("unlinkat")]
        #[on(X86, 301, I(32), Ptr, I(32))]
        #[on(X86_64, 263, I(32), Ptr, I(32))]
        #[on(Arm, 328, I(32), Ptr, I(32))]
        #[on(Aarch64, 35, I(32), Ptr, I(32))]
        Unlinkat,
        #[name("unshare")]
        #[on(X86, 310, UWord)]
        #[on(X86_64, 272, UWord)]
        #[on(Arm, 337, UWord)]
        #[on(Aarch64, 97, UWord)]
        Unshare,
        #[name("uprobe")]
        #[on(X86_64, 336)]
        Uprobe,
        #[name("uretprobe")]
        #[on(X86_64, 335)]
        Uretprobe,
        #[name("uselib")]
        #[on(X86, 86, Ptr)]
        #[on(X86_64, 134)]
        #[on(Arm, 86, Ptr)]
        Uselib,
        #[name("userfaultfd")]
        #[on(X86, 374, I(32))]
        #[on(X86_64, 323, I(32))]
        #[on(Arm, 388, I(32))]
        #[on(Aarch64, 282, I(32))]
        Userfaultfd,
        #[name("usr26")]
        #[on(Arm, 983043)]
        Usr26,
        #[name("usr32")]
        #[on(Arm, 983044)]
        Usr32,
        #[name("ustat")]
        #[on(X86, 62, U(32), Ptr)]
        #[on(X86_64, 136, U(32), Ptr)]
        #[on(Arm, 62, U(32), Ptr)]
        Ustat,
        #[name("utime")]
        #[on(X86, 30, Ptr, Ptr)]
        #[on(X86_64, 132, Ptr, Ptr)]
        Utime,
        #[name("utimensat")]
        #[on(X86, 320, U(32), Ptr, Ptr, I(32))]
        #[on(X86_64, 280, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 348, U(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 88, I(32), Ptr, Ptr, I(32))]
        Utimensat,
        #[name("utimensat_time64")]
        #[on(X86, 412, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 412, I(32), Ptr, Ptr, I(32))]
        UtimensatTime64,
        #[name("utimes")]
        #[on(X86, 271, Ptr, Ptr)]
        #[on(X86_64, 235, Ptr, Ptr)]
        #[on(Arm, 269, Ptr, Ptr)]
        Utimes,
        #[name("vfork")]
        #[on(X86, 190)]
        #[on(X86_64, 58)]
        #[on(Arm, 190)]
        Vfork,
        #[name("vhangup")]
        #[on(X86, 111)]
        #[on(X86_64, 153)]
        #[on(Arm, 111)]
        #[on(Aarch64, 58)]
        Vhangup,
        #[name("vm86")]
        #[on(X86, 166, UWord, UWord)]
        Vm86,
        #[name("vm86old")]
        #[on(X86, 113, Ptr)]
        Vm86old,
        #[name("vmsplice")]
        #[on(X86, 316, I(32), Ptr, UWord, U(32))]
        #[on(X86_64, 278, I(32), Ptr, UWord, U(32))]
        #[on(Arm, 343, I(32), Ptr, UWord, U(32))]
        #[on(Aarch64, 75, I(32), Ptr, UWord, U(32))]
        Vmsplice,
        #[name("vserver")]
        #[on(X86, 273)]
        #[on(X86_64, 236)]
        #[on(Arm, 313)]
        Vserver,
        #[name("wait4")]
        #[on(X86, 114, I(32), Ptr, I(32), Ptr)]
        #[on(X86_64, 61, I(32), Ptr, I(32), Ptr)]
        #[on(Arm, 114, I(32), Ptr, I(32), Ptr)]
        #[on(Aarch64, 260, I(32), Ptr, I(32), Ptr)]
        Wait4,
        #[name("waitid")]
        #[on(X86, 284, I(32), I(32), Ptr, I(32), Ptr)]
        #[on(X86_64, 247, I(32), I(32), Ptr, I(32), Ptr)]
        #[on(Arm, 280, I(32), I(32), Ptr, I(32), Ptr)]
        #[on(Aarch64, 95, I(32), I(32), Ptr, I(32), Ptr)]
        Waitid,
        #[name("waitpid")]
        #[on(X86, 7, I(32), Ptr, I(32))]
        Waitpid,
        #[name("write")]
        #[on(X86, 4, U(32), Ptr, UWord)]
        #[on(X86_64, 1, U(32), Ptr, UWord)]
        #[on(Arm, 4, U(32), Ptr, UWord)]
        #[on(Aarch64, 64, U(32), Ptr, UWord)]
        Write,
        #[name("writev")]
        #[on(X86, 146, UWord, Ptr, UWord)]
        #[on(X86_64, 20, UWord, Ptr, UWord)]
        #[on(Arm, 146, UWord, Ptr, UWord)]
        #[on(Aarch64, 66, UWord, Ptr, UWord)]
        Writev,
    }
}
