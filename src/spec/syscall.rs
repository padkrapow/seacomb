use vstd::prelude::*;
use super::expr::PrimType;
 
verus! {

/// A helper macro to define the `Syscall` enum and its `Syscall::nr` and
/// `Syscall::signature` functions.
macro_rules! syscalls {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $(
                $( #[on($arch:ident, $nr:expr $(, $ty:ident $(($width:literal))?)*)] )*
                $variant:ident
            ),* $(,)?
        }
    ) => {
        verus! {
            $(#[$meta])*
            $vis enum $name {
                $( $variant, )*
            }

            impl $name {
                #[allow(unreachable_patterns)]
                #[verifier::opaque]
                pub open spec fn spec_nr(&self, arch: super::policy::Arch) -> Option<i32> {
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( super::policy::Arch::$arch => Some(($nr) as i32), )*
                                _ => None,
                            },
                        )*
                    }
                }

                /// Executable version of [`Self::spec_nr`].
                #[allow(unreachable_patterns)]
                #[verifier::when_used_as_spec(spec_nr)]
                pub fn nr(&self, arch: super::policy::Arch) -> (res: Option<i32>)
                    ensures res == self.spec_nr(arch)
                {
                    reveal($name::spec_nr);
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( super::policy::Arch::$arch => Some(($nr) as i32), )*
                                _ => None,
                            },
                        )*
                    }
                }

                /// Argument types on `arch`, empty if the syscall does not exist there.
                #[allow(unreachable_patterns)]
                #[verifier::opaque]
                pub open spec fn spec_signature(&self, arch: super::policy::Arch) -> Seq<PrimType> {
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( super::policy::Arch::$arch => seq![$( PrimType::$ty $(($width))? ),*], )*
                                _ => Seq::empty(),
                            },
                        )*
                    }
                }

                /// Executable version of [`Self::spec_signature`].
                #[allow(unreachable_patterns)]
                pub fn signature(&self, arch: super::policy::Arch) -> (res: &'static [PrimType])
                    ensures res@ =~= self.spec_signature(arch)
                {
                    reveal(Syscall::spec_signature);
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( super::policy::Arch::$arch => &[$( PrimType::$ty $(($width))? ),*], )*
                                _ => &[],
                            },
                        )*
                    }
                }
            }
        }
    };
}

syscalls! {
    /// Linux syscall identifiers, extracted from Linux v7.0.
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
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
    pub enum Syscall {
        #[on(X86_64, 43, I(32), Ptr, Ptr)]
        #[on(Arm, 285, I(32), Ptr, Ptr)]
        #[on(Aarch64, 202, I(32), Ptr, Ptr)]
        Accept,
        #[on(X86, 364, I(32), Ptr, Ptr, I(32))]
        #[on(X86_64, 288, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 366, I(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 242, I(32), Ptr, Ptr, I(32))]
        Accept4,
        #[on(X86, 33, Ptr, I(32))]
        #[on(X86_64, 21, Ptr, I(32))]
        #[on(Arm, 33, Ptr, I(32))]
        Access,
        #[on(X86, 51, Ptr)]
        #[on(X86_64, 163, Ptr)]
        #[on(Arm, 51, Ptr)]
        #[on(Aarch64, 89, Ptr)]
        Acct,
        #[on(X86, 286, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(X86_64, 248, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Arm, 309, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Aarch64, 217, Ptr, Ptr, Ptr, UWord, I(32))]
        AddKey,
        #[on(X86, 124, Ptr)]
        #[on(X86_64, 159, Ptr)]
        #[on(Arm, 124, Ptr)]
        #[on(Aarch64, 171, Ptr)]
        Adjtimex,
        #[on(X86, 137)]
        #[on(X86_64, 183)]
        AfsSyscall,
        #[on(X86, 27, U(32))]
        #[on(X86_64, 37, U(32))]
        Alarm,
        #[on(X86, 384, I(32), UWord)]
        #[on(X86_64, 158, I(32), UWord)]
        ArchPrctl,
        #[on(Arm, 270, I(32), I(32), I(64), I(64))]
        ArmFadvise64_64,
        #[on(Arm, 341, I(32), U(32), I(64), I(64))]
        ArmSyncFileRange,
        #[on(X86, 134)]
        #[on(Arm, 134)]
        Bdflush,
        #[on(X86, 361, I(32), Ptr, I(32))]
        #[on(X86_64, 49, I(32), Ptr, I(32))]
        #[on(Arm, 282, I(32), Ptr, I(32))]
        #[on(Aarch64, 200, I(32), Ptr, I(32))]
        Bind,
        #[on(X86, 357, I(32), Ptr, U(32))]
        #[on(X86_64, 321, I(32), Ptr, U(32))]
        #[on(Arm, 386, I(32), Ptr, U(32))]
        #[on(Aarch64, 280, I(32), Ptr, U(32))]
        Bpf,
        #[on(X86, 17)]
        Break,
        #[on(Arm, 983041)]
        Breakpoint,
        #[on(X86, 45, UWord)]
        #[on(X86_64, 12, UWord)]
        #[on(Arm, 45, UWord)]
        #[on(Aarch64, 214, UWord)]
        Brk,
        #[on(Arm, 983042, UWord, UWord, I(32))]
        Cacheflush,
        #[on(X86, 451, U(32), Ptr, Ptr, U(32))]
        #[on(X86_64, 451, U(32), Ptr, Ptr, U(32))]
        #[on(Arm, 451, U(32), Ptr, Ptr, U(32))]
        #[on(Aarch64, 451, U(32), Ptr, Ptr, U(32))]
        Cachestat,
        #[on(X86, 184, Ptr, Ptr)]
        #[on(X86_64, 125, Ptr, Ptr)]
        #[on(Arm, 184, Ptr, Ptr)]
        #[on(Aarch64, 90, Ptr, Ptr)]
        Capget,
        #[on(X86, 185, Ptr, Ptr)]
        #[on(X86_64, 126, Ptr, Ptr)]
        #[on(Arm, 185, Ptr, Ptr)]
        #[on(Aarch64, 91, Ptr, Ptr)]
        Capset,
        #[on(X86, 12, Ptr)]
        #[on(X86_64, 80, Ptr)]
        #[on(Arm, 12, Ptr)]
        #[on(Aarch64, 49, Ptr)]
        Chdir,
        #[on(X86, 15, Ptr, U(16))]
        #[on(X86_64, 90, Ptr, U(16))]
        #[on(Arm, 15, Ptr, U(16))]
        Chmod,
        #[on(X86, 182, Ptr, U(16), U(16))]
        #[on(X86_64, 92, Ptr, U(32), U(32))]
        #[on(Arm, 182, Ptr, U(16), U(16))]
        Chown,
        #[on(X86, 212, Ptr, U(32), U(32))]
        #[on(Arm, 212, Ptr, U(32), U(32))]
        Chown32,
        #[on(X86, 61, Ptr)]
        #[on(X86_64, 161, Ptr)]
        #[on(Arm, 61, Ptr)]
        #[on(Aarch64, 51, Ptr)]
        Chroot,
        #[on(X86, 343, I(32), Ptr)]
        #[on(X86_64, 305, I(32), Ptr)]
        #[on(Arm, 372, I(32), Ptr)]
        #[on(Aarch64, 266, I(32), Ptr)]
        ClockAdjtime,
        #[on(X86, 405, I(32), Ptr)]
        #[on(Arm, 405, I(32), Ptr)]
        ClockAdjtime64,
        #[on(X86, 266, I(32), Ptr)]
        #[on(X86_64, 229, I(32), Ptr)]
        #[on(Arm, 264, I(32), Ptr)]
        #[on(Aarch64, 114, I(32), Ptr)]
        ClockGetres,
        #[on(X86, 406, I(32), Ptr)]
        #[on(Arm, 406, I(32), Ptr)]
        ClockGetresTime64,
        #[on(X86, 265, I(32), Ptr)]
        #[on(X86_64, 228, I(32), Ptr)]
        #[on(Arm, 263, I(32), Ptr)]
        #[on(Aarch64, 113, I(32), Ptr)]
        ClockGettime,
        #[on(X86, 403, I(32), Ptr)]
        #[on(Arm, 403, I(32), Ptr)]
        ClockGettime64,
        #[on(X86, 267, I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 230, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 265, I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 115, I(32), I(32), Ptr, Ptr)]
        ClockNanosleep,
        #[on(X86, 407, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 407, I(32), I(32), Ptr, Ptr)]
        ClockNanosleepTime64,
        #[on(X86, 264, I(32), Ptr)]
        #[on(X86_64, 227, I(32), Ptr)]
        #[on(Arm, 262, I(32), Ptr)]
        #[on(Aarch64, 112, I(32), Ptr)]
        ClockSettime,
        #[on(X86, 404, I(32), Ptr)]
        #[on(Arm, 404, I(32), Ptr)]
        ClockSettime64,
        #[on(X86, 120, UWord, UWord, Ptr, UWord, Ptr)]
        #[on(X86_64, 56, UWord, UWord, Ptr, Ptr, UWord)]
        #[on(Arm, 120, UWord, UWord, Ptr, UWord, Ptr)]
        #[on(Aarch64, 220, UWord, UWord, Ptr, UWord, Ptr)]
        Clone,
        #[on(X86, 435, Ptr, UWord)]
        #[on(X86_64, 435, Ptr, UWord)]
        #[on(Arm, 435, Ptr, UWord)]
        #[on(Aarch64, 435, Ptr, UWord)]
        Clone3,
        #[on(X86, 6, U(32))]
        #[on(X86_64, 3, U(32))]
        #[on(Arm, 6, U(32))]
        #[on(Aarch64, 57, U(32))]
        Close,
        #[on(X86, 436, U(32), U(32), U(32))]
        #[on(X86_64, 436, U(32), U(32), U(32))]
        #[on(Arm, 436, U(32), U(32), U(32))]
        #[on(Aarch64, 436, U(32), U(32), U(32))]
        CloseRange,
        #[on(X86, 362, I(32), Ptr, I(32))]
        #[on(X86_64, 42, I(32), Ptr, I(32))]
        #[on(Arm, 283, I(32), Ptr, I(32))]
        #[on(Aarch64, 203, I(32), Ptr, I(32))]
        Connect,
        #[on(X86, 377, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(X86_64, 326, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(Arm, 391, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(Aarch64, 285, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        CopyFileRange,
        #[on(X86, 8, Ptr, U(16))]
        #[on(X86_64, 85, Ptr, U(16))]
        #[on(Arm, 8, Ptr, U(16))]
        Creat,
        #[on(X86, 127)]
        #[on(X86_64, 174)]
        CreateModule,
        #[on(X86, 129, Ptr, U(32))]
        #[on(X86_64, 176, Ptr, U(32))]
        #[on(Arm, 129, Ptr, U(32))]
        #[on(Aarch64, 106, Ptr, U(32))]
        DeleteModule,
        #[on(X86, 41, U(32))]
        #[on(X86_64, 32, U(32))]
        #[on(Arm, 41, U(32))]
        #[on(Aarch64, 23, U(32))]
        Dup,
        #[on(X86, 63, U(32), U(32))]
        #[on(X86_64, 33, U(32), U(32))]
        #[on(Arm, 63, U(32), U(32))]
        Dup2,
        #[on(X86, 330, U(32), U(32), I(32))]
        #[on(X86_64, 292, U(32), U(32), I(32))]
        #[on(Arm, 358, U(32), U(32), I(32))]
        #[on(Aarch64, 24, U(32), U(32), I(32))]
        Dup3,
        #[on(X86, 254, I(32))]
        #[on(X86_64, 213, I(32))]
        #[on(Arm, 250, I(32))]
        EpollCreate,
        #[on(X86, 329, I(32))]
        #[on(X86_64, 291, I(32))]
        #[on(Arm, 357, I(32))]
        #[on(Aarch64, 20, I(32))]
        EpollCreate1,
        #[on(X86, 255, I(32), I(32), I(32), Ptr)]
        #[on(X86_64, 233, I(32), I(32), I(32), Ptr)]
        #[on(Arm, 251, I(32), I(32), I(32), Ptr)]
        #[on(Aarch64, 21, I(32), I(32), I(32), Ptr)]
        EpollCtl,
        #[on(X86_64, 214)]
        EpollCtlOld,
        #[on(X86, 319, I(32), Ptr, I(32), I(32), Ptr, UWord)]
        #[on(X86_64, 281, I(32), Ptr, I(32), I(32), Ptr, UWord)]
        #[on(Arm, 346, I(32), Ptr, I(32), I(32), Ptr, UWord)]
        #[on(Aarch64, 22, I(32), Ptr, I(32), I(32), Ptr, UWord)]
        EpollPwait,
        #[on(X86, 441, I(32), Ptr, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 441, I(32), Ptr, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 441, I(32), Ptr, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 441, I(32), Ptr, I(32), Ptr, Ptr, UWord)]
        EpollPwait2,
        #[on(X86, 256, I(32), Ptr, I(32), I(32))]
        #[on(X86_64, 232, I(32), Ptr, I(32), I(32))]
        #[on(Arm, 252, I(32), Ptr, I(32), I(32))]
        EpollWait,
        #[on(X86_64, 215)]
        EpollWaitOld,
        #[on(X86, 323, U(32))]
        #[on(X86_64, 284, U(32))]
        #[on(Arm, 351, U(32))]
        Eventfd,
        #[on(X86, 328, U(32), I(32))]
        #[on(X86_64, 290, U(32), I(32))]
        #[on(Arm, 356, U(32), I(32))]
        #[on(Aarch64, 19, U(32), I(32))]
        Eventfd2,
        #[on(X86, 11, Ptr, Ptr, Ptr)]
        #[on(X86_64, 59, Ptr, Ptr, Ptr)]
        #[on(Arm, 11, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 221, Ptr, Ptr, Ptr)]
        Execve,
        #[on(X86, 358, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(X86_64, 322, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(Arm, 387, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(Aarch64, 281, I(32), Ptr, Ptr, Ptr, I(32))]
        Execveat,
        #[on(X86, 1, I(32))]
        #[on(X86_64, 60, I(32))]
        #[on(Arm, 1, I(32))]
        #[on(Aarch64, 93, I(32))]
        Exit,
        #[on(X86, 252, I(32))]
        #[on(X86_64, 231, I(32))]
        #[on(Arm, 248, I(32))]
        #[on(Aarch64, 94, I(32))]
        ExitGroup,
        #[on(X86, 307, I(32), Ptr, I(32))]
        #[on(X86_64, 269, I(32), Ptr, I(32))]
        #[on(Arm, 334, I(32), Ptr, I(32))]
        #[on(Aarch64, 48, I(32), Ptr, I(32))]
        Faccessat,
        #[on(X86, 439, I(32), Ptr, I(32), I(32))]
        #[on(X86_64, 439, I(32), Ptr, I(32), I(32))]
        #[on(Arm, 439, I(32), Ptr, I(32), I(32))]
        #[on(Aarch64, 439, I(32), Ptr, I(32), I(32))]
        Faccessat2,
        #[on(X86, 250, I(32), I(64), UWord, I(32))]
        #[on(X86_64, 221, I(32), I(64), UWord, I(32))]
        #[on(Aarch64, 223, I(32), I(64), I(64), I(32))]
        Fadvise64,
        #[on(X86, 272, I(32), I(64), I(64), I(32))]
        Fadvise64_64,
        #[on(X86, 324, I(32), I(32), I(64), I(64))]
        #[on(X86_64, 285, I(32), I(32), I(64), I(64))]
        #[on(Arm, 352, I(32), I(32), I(64), I(64))]
        #[on(Aarch64, 47, I(32), I(32), I(64), I(64))]
        Fallocate,
        #[on(X86, 338, U(32), U(32))]
        #[on(X86_64, 300, U(32), U(32))]
        #[on(Arm, 367, U(32), U(32))]
        #[on(Aarch64, 262, U(32), U(32))]
        FanotifyInit,
        #[on(X86, 339, I(32), U(32), U(64), I(32), Ptr)]
        #[on(X86_64, 301, I(32), U(32), U(64), I(32), Ptr)]
        #[on(Arm, 368, I(32), U(32), U(64), I(32), Ptr)]
        #[on(Aarch64, 263, I(32), U(32), U(64), I(32), Ptr)]
        FanotifyMark,
        #[on(X86, 133, U(32))]
        #[on(X86_64, 81, U(32))]
        #[on(Arm, 133, U(32))]
        #[on(Aarch64, 50, U(32))]
        Fchdir,
        #[on(X86, 94, U(32), U(16))]
        #[on(X86_64, 91, U(32), U(16))]
        #[on(Arm, 94, U(32), U(16))]
        #[on(Aarch64, 52, U(32), U(16))]
        Fchmod,
        #[on(X86, 306, I(32), Ptr, U(16))]
        #[on(X86_64, 268, I(32), Ptr, U(16))]
        #[on(Arm, 333, I(32), Ptr, U(16))]
        #[on(Aarch64, 53, I(32), Ptr, U(16))]
        Fchmodat,
        #[on(X86, 452, I(32), Ptr, U(16), U(32))]
        #[on(X86_64, 452, I(32), Ptr, U(16), U(32))]
        #[on(Arm, 452, I(32), Ptr, U(16), U(32))]
        #[on(Aarch64, 452, I(32), Ptr, U(16), U(32))]
        Fchmodat2,
        #[on(X86, 95, U(32), U(16), U(16))]
        #[on(X86_64, 93, U(32), U(32), U(32))]
        #[on(Arm, 95, U(32), U(16), U(16))]
        #[on(Aarch64, 55, U(32), U(32), U(32))]
        Fchown,
        #[on(X86, 207, U(32), U(32), U(32))]
        #[on(Arm, 207, U(32), U(32), U(32))]
        Fchown32,
        #[on(X86, 298, I(32), Ptr, U(32), U(32), I(32))]
        #[on(X86_64, 260, I(32), Ptr, U(32), U(32), I(32))]
        #[on(Arm, 325, I(32), Ptr, U(32), U(32), I(32))]
        #[on(Aarch64, 54, I(32), Ptr, U(32), U(32), I(32))]
        Fchownat,
        #[on(X86, 55, U(32), U(32), UWord)]
        #[on(X86_64, 72, U(32), U(32), UWord)]
        #[on(Arm, 55, U(32), U(32), UWord)]
        #[on(Aarch64, 25, U(32), U(32), UWord)]
        Fcntl,
        #[on(X86, 221, U(32), U(32), UWord)]
        #[on(Arm, 221, U(32), U(32), UWord)]
        Fcntl64,
        #[on(X86, 148, U(32))]
        #[on(X86_64, 75, U(32))]
        #[on(Arm, 148, U(32))]
        #[on(Aarch64, 83, U(32))]
        Fdatasync,
        #[on(X86, 231, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 193, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 231, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 10, I(32), Ptr, Ptr, UWord)]
        Fgetxattr,
        #[on(X86, 468, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 468, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 468, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 468, I(32), Ptr, Ptr, UWord, U(32))]
        FileGetattr,
        #[on(X86, 469, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 469, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 469, I(32), Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 469, I(32), Ptr, Ptr, UWord, U(32))]
        FileSetattr,
        #[on(X86, 350, I(32), Ptr, I(32))]
        #[on(X86_64, 313, I(32), Ptr, I(32))]
        #[on(Arm, 379, I(32), Ptr, I(32))]
        #[on(Aarch64, 273, I(32), Ptr, I(32))]
        FinitModule,
        #[on(X86, 234, I(32), Ptr, UWord)]
        #[on(X86_64, 196, I(32), Ptr, UWord)]
        #[on(Arm, 234, I(32), Ptr, UWord)]
        #[on(Aarch64, 13, I(32), Ptr, UWord)]
        Flistxattr,
        #[on(X86, 143, U(32), U(32))]
        #[on(X86_64, 73, U(32), U(32))]
        #[on(Arm, 143, U(32), U(32))]
        #[on(Aarch64, 32, U(32), U(32))]
        Flock,
        #[on(X86, 2)]
        #[on(X86_64, 57)]
        #[on(Arm, 2)]
        Fork,
        #[on(X86, 237, I(32), Ptr)]
        #[on(X86_64, 199, I(32), Ptr)]
        #[on(Arm, 237, I(32), Ptr)]
        #[on(Aarch64, 16, I(32), Ptr)]
        Fremovexattr,
        #[on(X86, 431, I(32), U(32), Ptr, Ptr, I(32))]
        #[on(X86_64, 431, I(32), U(32), Ptr, Ptr, I(32))]
        #[on(Arm, 431, I(32), U(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 431, I(32), U(32), Ptr, Ptr, I(32))]
        Fsconfig,
        #[on(X86, 228, I(32), Ptr, Ptr, UWord, I(32))]
        #[on(X86_64, 190, I(32), Ptr, Ptr, UWord, I(32))]
        #[on(Arm, 228, I(32), Ptr, Ptr, UWord, I(32))]
        #[on(Aarch64, 7, I(32), Ptr, Ptr, UWord, I(32))]
        Fsetxattr,
        #[on(X86, 432, I(32), U(32), U(32))]
        #[on(X86_64, 432, I(32), U(32), U(32))]
        #[on(Arm, 432, I(32), U(32), U(32))]
        #[on(Aarch64, 432, I(32), U(32), U(32))]
        Fsmount,
        #[on(X86, 430, Ptr, U(32))]
        #[on(X86_64, 430, Ptr, U(32))]
        #[on(Arm, 430, Ptr, U(32))]
        #[on(Aarch64, 430, Ptr, U(32))]
        Fsopen,
        #[on(X86, 433, I(32), Ptr, U(32))]
        #[on(X86_64, 433, I(32), Ptr, U(32))]
        #[on(Arm, 433, I(32), Ptr, U(32))]
        #[on(Aarch64, 433, I(32), Ptr, U(32))]
        Fspick,
        #[on(X86, 108, U(32), Ptr)]
        #[on(X86_64, 5, U(32), Ptr)]
        #[on(Arm, 108, U(32), Ptr)]
        #[on(Aarch64, 80, U(32), Ptr)]
        Fstat,
        #[on(X86, 197, UWord, Ptr)]
        #[on(Arm, 197, UWord, Ptr)]
        Fstat64,
        #[on(X86, 300, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 327, I(32), Ptr, Ptr, I(32))]
        Fstatat64,
        #[on(X86, 100, U(32), Ptr)]
        #[on(X86_64, 138, U(32), Ptr)]
        #[on(Arm, 100, U(32), Ptr)]
        #[on(Aarch64, 44, U(32), Ptr)]
        Fstatfs,
        #[on(X86, 269, U(32), UWord, Ptr)]
        #[on(Arm, 267, U(32), UWord, Ptr)]
        Fstatfs64,
        #[on(X86, 118, U(32))]
        #[on(X86_64, 74, U(32))]
        #[on(Arm, 118, U(32))]
        #[on(Aarch64, 82, U(32))]
        Fsync,
        #[on(X86, 35)]
        Ftime,
        #[on(X86, 93, U(32), IWord)]
        #[on(X86_64, 77, U(32), IWord)]
        #[on(Arm, 93, U(32), IWord)]
        #[on(Aarch64, 46, U(32), IWord)]
        Ftruncate,
        #[on(X86, 194, U(32), I(64))]
        #[on(Arm, 194, U(32), I(64))]
        Ftruncate64,
        #[on(X86, 240, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        #[on(X86_64, 202, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        #[on(Arm, 240, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        #[on(Aarch64, 98, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        Futex,
        #[on(X86, 456, Ptr, U(32), I(32), I(32))]
        #[on(X86_64, 456, Ptr, U(32), I(32), I(32))]
        #[on(Arm, 456, Ptr, U(32), I(32), I(32))]
        #[on(Aarch64, 456, Ptr, U(32), I(32), I(32))]
        FutexRequeue,
        #[on(X86, 422, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        #[on(Arm, 422, Ptr, I(32), U(32), Ptr, Ptr, U(32))]
        FutexTime64,
        #[on(X86, 455, Ptr, UWord, UWord, U(32), Ptr, I(32))]
        #[on(X86_64, 455, Ptr, UWord, UWord, U(32), Ptr, I(32))]
        #[on(Arm, 455, Ptr, UWord, UWord, U(32), Ptr, I(32))]
        #[on(Aarch64, 455, Ptr, UWord, UWord, U(32), Ptr, I(32))]
        FutexWait,
        #[on(X86, 449, Ptr, U(32), U(32), Ptr, I(32))]
        #[on(X86_64, 449, Ptr, U(32), U(32), Ptr, I(32))]
        #[on(Arm, 449, Ptr, U(32), U(32), Ptr, I(32))]
        #[on(Aarch64, 449, Ptr, U(32), U(32), Ptr, I(32))]
        FutexWaitv,
        #[on(X86, 454, Ptr, UWord, I(32), U(32))]
        #[on(X86_64, 454, Ptr, UWord, I(32), U(32))]
        #[on(Arm, 454, Ptr, UWord, I(32), U(32))]
        #[on(Aarch64, 454, Ptr, UWord, I(32), U(32))]
        FutexWake,
        #[on(X86, 299, U(32), Ptr, Ptr)]
        #[on(X86_64, 261, I(32), Ptr, Ptr)]
        #[on(Arm, 326, U(32), Ptr, Ptr)]
        Futimesat,
        #[on(X86, 318, Ptr, Ptr, Ptr)]
        #[on(X86_64, 309, Ptr, Ptr, Ptr)]
        #[on(Arm, 345, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 168, Ptr, Ptr, Ptr)]
        Getcpu,
        #[on(X86, 183, Ptr, UWord)]
        #[on(X86_64, 79, Ptr, UWord)]
        #[on(Arm, 183, Ptr, UWord)]
        #[on(Aarch64, 17, Ptr, UWord)]
        Getcwd,
        #[on(X86, 141, U(32), Ptr, U(32))]
        #[on(X86_64, 78, U(32), Ptr, U(32))]
        #[on(Arm, 141, U(32), Ptr, U(32))]
        Getdents,
        #[on(X86, 220, U(32), Ptr, U(32))]
        #[on(X86_64, 217, U(32), Ptr, U(32))]
        #[on(Arm, 217, U(32), Ptr, U(32))]
        #[on(Aarch64, 61, U(32), Ptr, U(32))]
        Getdents64,
        #[on(X86, 50)]
        #[on(X86_64, 108)]
        #[on(Arm, 50)]
        #[on(Aarch64, 177)]
        Getegid,
        #[on(X86, 202)]
        #[on(Arm, 202)]
        Getegid32,
        #[on(X86, 49)]
        #[on(X86_64, 107)]
        #[on(Arm, 49)]
        #[on(Aarch64, 175)]
        Geteuid,
        #[on(X86, 201)]
        #[on(Arm, 201)]
        Geteuid32,
        #[on(X86, 47)]
        #[on(X86_64, 104)]
        #[on(Arm, 47)]
        #[on(Aarch64, 176)]
        Getgid,
        #[on(X86, 200)]
        #[on(Arm, 200)]
        Getgid32,
        #[on(X86, 80, I(32), Ptr)]
        #[on(X86_64, 115, I(32), Ptr)]
        #[on(Arm, 80, I(32), Ptr)]
        #[on(Aarch64, 158, I(32), Ptr)]
        Getgroups,
        #[on(X86, 205, I(32), Ptr)]
        #[on(Arm, 205, I(32), Ptr)]
        Getgroups32,
        #[on(X86, 105, I(32), Ptr)]
        #[on(X86_64, 36, I(32), Ptr)]
        #[on(Arm, 105, I(32), Ptr)]
        #[on(Aarch64, 102, I(32), Ptr)]
        Getitimer,
        #[on(X86, 130)]
        #[on(X86_64, 177)]
        GetKernelSyms,
        #[on(X86, 275, Ptr, Ptr, UWord, UWord, UWord)]
        #[on(X86_64, 239, Ptr, Ptr, UWord, UWord, UWord)]
        #[on(Arm, 320, Ptr, Ptr, UWord, UWord, UWord)]
        #[on(Aarch64, 236, Ptr, Ptr, UWord, UWord, UWord)]
        GetMempolicy,
        #[on(X86, 368, I(32), Ptr, Ptr)]
        #[on(X86_64, 52, I(32), Ptr, Ptr)]
        #[on(Arm, 287, I(32), Ptr, Ptr)]
        #[on(Aarch64, 205, I(32), Ptr, Ptr)]
        Getpeername,
        #[on(X86, 132, I(32))]
        #[on(X86_64, 121, I(32))]
        #[on(Arm, 132, I(32))]
        #[on(Aarch64, 155, I(32))]
        Getpgid,
        #[on(X86, 65)]
        #[on(X86_64, 111)]
        #[on(Arm, 65)]
        Getpgrp,
        #[on(X86, 20)]
        #[on(X86_64, 39)]
        #[on(Arm, 20)]
        #[on(Aarch64, 172)]
        Getpid,
        #[on(X86, 188)]
        #[on(X86_64, 181)]
        Getpmsg,
        #[on(X86, 64)]
        #[on(X86_64, 110)]
        #[on(Arm, 64)]
        #[on(Aarch64, 173)]
        Getppid,
        #[on(X86, 96, I(32), I(32))]
        #[on(X86_64, 140, I(32), I(32))]
        #[on(Arm, 96, I(32), I(32))]
        #[on(Aarch64, 141, I(32), I(32))]
        Getpriority,
        #[on(X86, 355, Ptr, UWord, U(32))]
        #[on(X86_64, 318, Ptr, UWord, U(32))]
        #[on(Arm, 384, Ptr, UWord, U(32))]
        #[on(Aarch64, 278, Ptr, UWord, U(32))]
        Getrandom,
        #[on(X86, 171, Ptr, Ptr, Ptr)]
        #[on(X86_64, 120, Ptr, Ptr, Ptr)]
        #[on(Arm, 171, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 150, Ptr, Ptr, Ptr)]
        Getresgid,
        #[on(X86, 211, Ptr, Ptr, Ptr)]
        #[on(Arm, 211, Ptr, Ptr, Ptr)]
        Getresgid32,
        #[on(X86, 165, Ptr, Ptr, Ptr)]
        #[on(X86_64, 118, Ptr, Ptr, Ptr)]
        #[on(Arm, 165, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 148, Ptr, Ptr, Ptr)]
        Getresuid,
        #[on(X86, 209, Ptr, Ptr, Ptr)]
        #[on(Arm, 209, Ptr, Ptr, Ptr)]
        Getresuid32,
        #[on(X86, 76, U(32), Ptr)]
        #[on(X86_64, 97, U(32), Ptr)]
        #[on(Aarch64, 163, U(32), Ptr)]
        Getrlimit,
        #[on(X86, 312, I(32), Ptr, Ptr)]
        #[on(X86_64, 274, I(32), Ptr, Ptr)]
        #[on(Arm, 339, I(32), Ptr, Ptr)]
        #[on(Aarch64, 100, I(32), Ptr, Ptr)]
        GetRobustList,
        #[on(X86, 77, I(32), Ptr)]
        #[on(X86_64, 98, I(32), Ptr)]
        #[on(Arm, 77, I(32), Ptr)]
        #[on(Aarch64, 165, I(32), Ptr)]
        Getrusage,
        #[on(X86, 147, I(32))]
        #[on(X86_64, 124, I(32))]
        #[on(Arm, 147, I(32))]
        #[on(Aarch64, 156, I(32))]
        Getsid,
        #[on(X86, 367, I(32), Ptr, Ptr)]
        #[on(X86_64, 51, I(32), Ptr, Ptr)]
        #[on(Arm, 286, I(32), Ptr, Ptr)]
        #[on(Aarch64, 204, I(32), Ptr, Ptr)]
        Getsockname,
        #[on(X86, 365, I(32), I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 55, I(32), I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 295, I(32), I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 209, I(32), I(32), I(32), Ptr, Ptr)]
        Getsockopt,
        #[on(X86, 244, Ptr)]
        #[on(X86_64, 211)]
        GetThreadArea,
        #[on(X86, 224)]
        #[on(X86_64, 186)]
        #[on(Arm, 224)]
        #[on(Aarch64, 178)]
        Gettid,
        #[on(X86, 78, Ptr, Ptr)]
        #[on(X86_64, 96, Ptr, Ptr)]
        #[on(Arm, 78, Ptr, Ptr)]
        #[on(Aarch64, 169, Ptr, Ptr)]
        Gettimeofday,
        #[on(Arm, 983046)]
        GetTls,
        #[on(X86, 24)]
        #[on(X86_64, 102)]
        #[on(Arm, 24)]
        #[on(Aarch64, 174)]
        Getuid,
        #[on(X86, 199)]
        #[on(Arm, 199)]
        Getuid32,
        #[on(X86, 229, Ptr, Ptr, Ptr, UWord)]
        #[on(X86_64, 191, Ptr, Ptr, Ptr, UWord)]
        #[on(Arm, 229, Ptr, Ptr, Ptr, UWord)]
        #[on(Aarch64, 8, Ptr, Ptr, Ptr, UWord)]
        Getxattr,
        #[on(X86, 464, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 464, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Arm, 464, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 464, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        Getxattrat,
        #[on(X86, 32)]
        Gtty,
        #[on(X86, 112)]
        Idle,
        #[on(X86, 128, Ptr, UWord, Ptr)]
        #[on(X86_64, 175, Ptr, UWord, Ptr)]
        #[on(Arm, 128, Ptr, UWord, Ptr)]
        #[on(Aarch64, 105, Ptr, UWord, Ptr)]
        InitModule,
        #[on(X86, 292, I(32), Ptr, U(32))]
        #[on(X86_64, 254, I(32), Ptr, U(32))]
        #[on(Arm, 317, I(32), Ptr, U(32))]
        #[on(Aarch64, 27, I(32), Ptr, U(32))]
        InotifyAddWatch,
        #[on(X86, 291)]
        #[on(X86_64, 253)]
        #[on(Arm, 316)]
        InotifyInit,
        #[on(X86, 332, I(32))]
        #[on(X86_64, 294, I(32))]
        #[on(Arm, 360, I(32))]
        #[on(Aarch64, 26, I(32))]
        InotifyInit1,
        #[on(X86, 293, I(32), I(32))]
        #[on(X86_64, 255, I(32), I(32))]
        #[on(Arm, 318, I(32), I(32))]
        #[on(Aarch64, 28, I(32), I(32))]
        InotifyRmWatch,
        #[on(X86, 249, UWord, Ptr, Ptr)]
        #[on(X86_64, 210, UWord, Ptr, Ptr)]
        #[on(Arm, 247, UWord, Ptr, Ptr)]
        #[on(Aarch64, 3, UWord, Ptr, Ptr)]
        IoCancel,
        #[on(X86, 54, U(32), U(32), UWord)]
        #[on(X86_64, 16, U(32), U(32), UWord)]
        #[on(Arm, 54, U(32), U(32), UWord)]
        #[on(Aarch64, 29, U(32), U(32), UWord)]
        Ioctl,
        #[on(X86, 246, UWord)]
        #[on(X86_64, 207, UWord)]
        #[on(Arm, 244, UWord)]
        #[on(Aarch64, 1, UWord)]
        IoDestroy,
        #[on(X86, 247, U(32), I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 208, UWord, IWord, IWord, Ptr, Ptr)]
        #[on(Arm, 245, U(32), I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 4, UWord, IWord, IWord, Ptr, Ptr)]
        IoGetevents,
        #[on(X86, 101, UWord, UWord, I(32))]
        #[on(X86_64, 173, UWord, UWord, I(32))]
        Ioperm,
        #[on(X86, 385, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        #[on(X86_64, 333, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        #[on(Arm, 399, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 292, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        IoPgetevents,
        #[on(X86, 416, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        #[on(Arm, 416, UWord, IWord, IWord, Ptr, Ptr, Ptr)]
        IoPgeteventsTime64,
        #[on(X86, 110, U(32))]
        #[on(X86_64, 172, U(32))]
        Iopl,
        #[on(X86, 290, I(32), I(32))]
        #[on(X86_64, 252, I(32), I(32))]
        #[on(Arm, 315, I(32), I(32))]
        #[on(Aarch64, 31, I(32), I(32))]
        IoprioGet,
        #[on(X86, 289, I(32), I(32), I(32))]
        #[on(X86_64, 251, I(32), I(32), I(32))]
        #[on(Arm, 314, I(32), I(32), I(32))]
        #[on(Aarch64, 30, I(32), I(32), I(32))]
        IoprioSet,
        #[on(X86, 245, U(32), Ptr)]
        #[on(X86_64, 206, U(32), Ptr)]
        #[on(Arm, 243, U(32), Ptr)]
        #[on(Aarch64, 0, U(32), Ptr)]
        IoSetup,
        #[on(X86, 248, UWord, IWord, Ptr)]
        #[on(X86_64, 209, UWord, IWord, Ptr)]
        #[on(Arm, 246, UWord, IWord, Ptr)]
        #[on(Aarch64, 2, UWord, IWord, Ptr)]
        IoSubmit,
        #[on(X86, 426, U(32), U(32), U(32), U(32), Ptr, UWord)]
        #[on(X86_64, 426, U(32), U(32), U(32), U(32), Ptr, UWord)]
        #[on(Arm, 426, U(32), U(32), U(32), U(32), Ptr, UWord)]
        #[on(Aarch64, 426, U(32), U(32), U(32), U(32), Ptr, UWord)]
        IoUringEnter,
        #[on(X86, 427, U(32), U(32), Ptr, U(32))]
        #[on(X86_64, 427, U(32), U(32), Ptr, U(32))]
        #[on(Arm, 427, U(32), U(32), Ptr, U(32))]
        #[on(Aarch64, 427, U(32), U(32), Ptr, U(32))]
        IoUringRegister,
        #[on(X86, 425, U(32), Ptr)]
        #[on(X86_64, 425, U(32), Ptr)]
        #[on(Arm, 425, U(32), Ptr)]
        #[on(Aarch64, 425, U(32), Ptr)]
        IoUringSetup,
        #[on(X86, 117, U(32), I(32), UWord, UWord, Ptr, IWord)]
        Ipc,
        #[on(X86, 349, I(32), I(32), I(32), UWord, UWord)]
        #[on(X86_64, 312, I(32), I(32), I(32), UWord, UWord)]
        #[on(Arm, 378, I(32), I(32), I(32), UWord, UWord)]
        #[on(Aarch64, 272, I(32), I(32), I(32), UWord, UWord)]
        Kcmp,
        #[on(X86_64, 320, I(32), I(32), UWord, Ptr, UWord)]
        #[on(Arm, 401, I(32), I(32), UWord, Ptr, UWord)]
        #[on(Aarch64, 294, I(32), I(32), UWord, Ptr, UWord)]
        KexecFileLoad,
        #[on(X86, 283, UWord, UWord, Ptr, UWord)]
        #[on(X86_64, 246, UWord, UWord, Ptr, UWord)]
        #[on(Arm, 347, UWord, UWord, Ptr, UWord)]
        #[on(Aarch64, 104, UWord, UWord, Ptr, UWord)]
        KexecLoad,
        #[on(X86, 288, I(32), UWord, UWord, UWord, UWord)]
        #[on(X86_64, 250, I(32), UWord, UWord, UWord, UWord)]
        #[on(Arm, 311, I(32), UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 219, I(32), UWord, UWord, UWord, UWord)]
        Keyctl,
        #[on(X86, 37, I(32), I(32))]
        #[on(X86_64, 62, I(32), I(32))]
        #[on(Arm, 37, I(32), I(32))]
        #[on(Aarch64, 129, I(32), I(32))]
        Kill,
        #[on(X86, 445, I(32), U(32), Ptr, U(32))]
        #[on(X86_64, 445, I(32), U(32), Ptr, U(32))]
        #[on(Arm, 445, I(32), U(32), Ptr, U(32))]
        #[on(Aarch64, 445, I(32), U(32), Ptr, U(32))]
        LandlockAddRule,
        #[on(X86, 444, Ptr, UWord, U(32))]
        #[on(X86_64, 444, Ptr, UWord, U(32))]
        #[on(Arm, 444, Ptr, UWord, U(32))]
        #[on(Aarch64, 444, Ptr, UWord, U(32))]
        LandlockCreateRuleset,
        #[on(X86, 446, I(32), U(32))]
        #[on(X86_64, 446, I(32), U(32))]
        #[on(Arm, 446, I(32), U(32))]
        #[on(Aarch64, 446, I(32), U(32))]
        LandlockRestrictSelf,
        #[on(X86, 16, Ptr, U(16), U(16))]
        #[on(X86_64, 94, Ptr, U(32), U(32))]
        #[on(Arm, 16, Ptr, U(16), U(16))]
        Lchown,
        #[on(X86, 198, Ptr, U(32), U(32))]
        #[on(Arm, 198, Ptr, U(32), U(32))]
        Lchown32,
        #[on(X86, 230, Ptr, Ptr, Ptr, UWord)]
        #[on(X86_64, 192, Ptr, Ptr, Ptr, UWord)]
        #[on(Arm, 230, Ptr, Ptr, Ptr, UWord)]
        #[on(Aarch64, 9, Ptr, Ptr, Ptr, UWord)]
        Lgetxattr,
        #[on(X86, 9, Ptr, Ptr)]
        #[on(X86_64, 86, Ptr, Ptr)]
        #[on(Arm, 9, Ptr, Ptr)]
        Link,
        #[on(X86, 303, I(32), Ptr, I(32), Ptr, I(32))]
        #[on(X86_64, 265, I(32), Ptr, I(32), Ptr, I(32))]
        #[on(Arm, 330, I(32), Ptr, I(32), Ptr, I(32))]
        #[on(Aarch64, 37, I(32), Ptr, I(32), Ptr, I(32))]
        Linkat,
        #[on(X86, 363, I(32), I(32))]
        #[on(X86_64, 50, I(32), I(32))]
        #[on(Arm, 284, I(32), I(32))]
        #[on(Aarch64, 201, I(32), I(32))]
        Listen,
        #[on(X86, 458, Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 458, Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 458, Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 458, Ptr, Ptr, UWord, U(32))]
        Listmount,
        #[on(X86, 470, Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 470, Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 470, Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 470, Ptr, Ptr, UWord, U(32))]
        Listns,
        #[on(X86, 232, Ptr, Ptr, UWord)]
        #[on(X86_64, 194, Ptr, Ptr, UWord)]
        #[on(Arm, 232, Ptr, Ptr, UWord)]
        #[on(Aarch64, 11, Ptr, Ptr, UWord)]
        Listxattr,
        #[on(X86, 465, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(X86_64, 465, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Arm, 465, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Aarch64, 465, I(32), Ptr, U(32), Ptr, UWord)]
        Listxattrat,
        #[on(X86, 233, Ptr, Ptr, UWord)]
        #[on(X86_64, 195, Ptr, Ptr, UWord)]
        #[on(Arm, 233, Ptr, Ptr, UWord)]
        #[on(Aarch64, 12, Ptr, Ptr, UWord)]
        Llistxattr,
        #[on(X86, 140, U(32), UWord, UWord, Ptr, U(32))]
        #[on(Arm, 140, U(32), UWord, UWord, Ptr, U(32))]
        _Llseek,
        #[on(X86, 53)]
        Lock,
        #[on(X86, 253)]
        #[on(X86_64, 212)]
        #[on(Arm, 249)]
        #[on(Aarch64, 18)]
        LookupDcookie,
        #[on(X86, 236, Ptr, Ptr)]
        #[on(X86_64, 198, Ptr, Ptr)]
        #[on(Arm, 236, Ptr, Ptr)]
        #[on(Aarch64, 15, Ptr, Ptr)]
        Lremovexattr,
        #[on(X86, 19, U(32), IWord, U(32))]
        #[on(X86_64, 8, U(32), IWord, U(32))]
        #[on(Arm, 19, U(32), IWord, U(32))]
        #[on(Aarch64, 62, U(32), IWord, U(32))]
        Lseek,
        #[on(X86, 227, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(X86_64, 189, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Arm, 227, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Aarch64, 6, Ptr, Ptr, Ptr, UWord, I(32))]
        Lsetxattr,
        #[on(X86, 459, U(32), Ptr, Ptr, U(32))]
        #[on(X86_64, 459, U(32), Ptr, Ptr, U(32))]
        #[on(Arm, 459, U(32), Ptr, Ptr, U(32))]
        #[on(Aarch64, 459, U(32), Ptr, Ptr, U(32))]
        LsmGetSelfAttr,
        #[on(X86, 461, Ptr, Ptr, U(32))]
        #[on(X86_64, 461, Ptr, Ptr, U(32))]
        #[on(Arm, 461, Ptr, Ptr, U(32))]
        #[on(Aarch64, 461, Ptr, Ptr, U(32))]
        LsmListModules,
        #[on(X86, 460, U(32), Ptr, U(32), U(32))]
        #[on(X86_64, 460, U(32), Ptr, U(32), U(32))]
        #[on(Arm, 460, U(32), Ptr, U(32), U(32))]
        #[on(Aarch64, 460, U(32), Ptr, U(32), U(32))]
        LsmSetSelfAttr,
        #[on(X86, 107, Ptr, Ptr)]
        #[on(X86_64, 6, Ptr, Ptr)]
        #[on(Arm, 107, Ptr, Ptr)]
        Lstat,
        #[on(X86, 196, Ptr, Ptr)]
        #[on(Arm, 196, Ptr, Ptr)]
        Lstat64,
        #[on(X86, 219, UWord, UWord, I(32))]
        #[on(X86_64, 28, UWord, UWord, I(32))]
        #[on(Arm, 220, UWord, UWord, I(32))]
        #[on(Aarch64, 233, UWord, UWord, I(32))]
        Madvise,
        #[on(X86, 453, UWord, UWord, U(32))]
        #[on(X86_64, 453, UWord, UWord, U(32))]
        #[on(Arm, 453, UWord, UWord, U(32))]
        #[on(Aarch64, 453, UWord, UWord, U(32))]
        MapShadowStack,
        #[on(X86, 274, UWord, UWord, UWord, Ptr, UWord, U(32))]
        #[on(X86_64, 237, UWord, UWord, UWord, Ptr, UWord, U(32))]
        #[on(Arm, 319, UWord, UWord, UWord, Ptr, UWord, U(32))]
        #[on(Aarch64, 235, UWord, UWord, UWord, Ptr, UWord, U(32))]
        Mbind,
        #[on(X86, 375, I(32), U(32), I(32))]
        #[on(X86_64, 324, I(32), U(32), I(32))]
        #[on(Arm, 389, I(32), U(32), I(32))]
        #[on(Aarch64, 283, I(32), U(32), I(32))]
        Membarrier,
        #[on(X86, 356, Ptr, U(32))]
        #[on(X86_64, 319, Ptr, U(32))]
        #[on(Arm, 385, Ptr, U(32))]
        #[on(Aarch64, 279, Ptr, U(32))]
        MemfdCreate,
        #[on(X86, 447, U(32))]
        #[on(X86_64, 447, U(32))]
        #[on(Aarch64, 447, U(32))]
        MemfdSecret,
        #[on(X86, 294, I(32), UWord, Ptr, Ptr)]
        #[on(X86_64, 256, I(32), UWord, Ptr, Ptr)]
        #[on(Arm, 400, I(32), UWord, Ptr, Ptr)]
        #[on(Aarch64, 238, I(32), UWord, Ptr, Ptr)]
        MigratePages,
        #[on(X86, 218, UWord, UWord, Ptr)]
        #[on(X86_64, 27, UWord, UWord, Ptr)]
        #[on(Arm, 219, UWord, UWord, Ptr)]
        #[on(Aarch64, 232, UWord, UWord, Ptr)]
        Mincore,
        #[on(X86, 39, Ptr, U(16))]
        #[on(X86_64, 83, Ptr, U(16))]
        #[on(Arm, 39, Ptr, U(16))]
        Mkdir,
        #[on(X86, 296, I(32), Ptr, U(16))]
        #[on(X86_64, 258, I(32), Ptr, U(16))]
        #[on(Arm, 323, I(32), Ptr, U(16))]
        #[on(Aarch64, 34, I(32), Ptr, U(16))]
        Mkdirat,
        #[on(X86, 14, Ptr, U(16), U(32))]
        #[on(X86_64, 133, Ptr, U(16), U(32))]
        #[on(Arm, 14, Ptr, U(16), U(32))]
        Mknod,
        #[on(X86, 297, I(32), Ptr, U(16), U(32))]
        #[on(X86_64, 259, I(32), Ptr, U(16), U(32))]
        #[on(Arm, 324, I(32), Ptr, U(16), U(32))]
        #[on(Aarch64, 33, I(32), Ptr, U(16), U(32))]
        Mknodat,
        #[on(X86, 150, UWord, UWord)]
        #[on(X86_64, 149, UWord, UWord)]
        #[on(Arm, 150, UWord, UWord)]
        #[on(Aarch64, 228, UWord, UWord)]
        Mlock,
        #[on(X86, 376, UWord, UWord, I(32))]
        #[on(X86_64, 325, UWord, UWord, I(32))]
        #[on(Arm, 390, UWord, UWord, I(32))]
        #[on(Aarch64, 284, UWord, UWord, I(32))]
        Mlock2,
        #[on(X86, 152, I(32))]
        #[on(X86_64, 151, I(32))]
        #[on(Arm, 152, I(32))]
        #[on(Aarch64, 230, I(32))]
        Mlockall,
        #[on(X86, 90, Ptr)]
        #[on(X86_64, 9, UWord, UWord, UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 222, UWord, UWord, UWord, UWord, UWord, UWord)]
        Mmap,
        #[on(X86, 192, UWord, UWord, UWord, UWord, UWord, UWord)]
        #[on(Arm, 192, UWord, UWord, UWord, UWord, UWord, UWord)]
        Mmap2,
        #[on(X86, 123, I(32), Ptr, UWord)]
        #[on(X86_64, 154, I(32), Ptr, UWord)]
        ModifyLdt,
        #[on(X86, 21, Ptr, Ptr, Ptr, UWord, Ptr)]
        #[on(X86_64, 165, Ptr, Ptr, Ptr, UWord, Ptr)]
        #[on(Arm, 21, Ptr, Ptr, Ptr, UWord, Ptr)]
        #[on(Aarch64, 40, Ptr, Ptr, Ptr, UWord, Ptr)]
        Mount,
        #[on(X86, 442, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(X86_64, 442, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Arm, 442, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Aarch64, 442, I(32), Ptr, U(32), Ptr, UWord)]
        MountSetattr,
        #[on(X86, 429, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(X86_64, 429, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(Arm, 429, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(Aarch64, 429, I(32), Ptr, I(32), Ptr, U(32))]
        MoveMount,
        #[on(X86, 317, I(32), UWord, Ptr, Ptr, Ptr, I(32))]
        #[on(X86_64, 279, I(32), UWord, Ptr, Ptr, Ptr, I(32))]
        #[on(Arm, 344, I(32), UWord, Ptr, Ptr, Ptr, I(32))]
        #[on(Aarch64, 239, I(32), UWord, Ptr, Ptr, Ptr, I(32))]
        MovePages,
        #[on(X86, 125, UWord, UWord, UWord)]
        #[on(X86_64, 10, UWord, UWord, UWord)]
        #[on(Arm, 125, UWord, UWord, UWord)]
        #[on(Aarch64, 226, UWord, UWord, UWord)]
        Mprotect,
        #[on(X86, 56)]
        Mpx,
        #[on(X86, 282, I(32), Ptr, Ptr)]
        #[on(X86_64, 245, I(32), Ptr, Ptr)]
        #[on(Arm, 279, I(32), Ptr, Ptr)]
        #[on(Aarch64, 185, I(32), Ptr, Ptr)]
        MqGetsetattr,
        #[on(X86, 281, I(32), Ptr)]
        #[on(X86_64, 244, I(32), Ptr)]
        #[on(Arm, 278, I(32), Ptr)]
        #[on(Aarch64, 184, I(32), Ptr)]
        MqNotify,
        #[on(X86, 277, Ptr, I(32), U(16), Ptr)]
        #[on(X86_64, 240, Ptr, I(32), U(16), Ptr)]
        #[on(Arm, 274, Ptr, I(32), U(16), Ptr)]
        #[on(Aarch64, 180, Ptr, I(32), U(16), Ptr)]
        MqOpen,
        #[on(X86, 280, I(32), Ptr, U(32), Ptr, Ptr)]
        #[on(X86_64, 243, I(32), Ptr, UWord, Ptr, Ptr)]
        #[on(Arm, 277, I(32), Ptr, U(32), Ptr, Ptr)]
        #[on(Aarch64, 183, I(32), Ptr, UWord, Ptr, Ptr)]
        MqTimedreceive,
        #[on(X86, 419, I(32), Ptr, UWord, Ptr, Ptr)]
        #[on(Arm, 419, I(32), Ptr, UWord, Ptr, Ptr)]
        MqTimedreceiveTime64,
        #[on(X86, 279, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(X86_64, 242, I(32), Ptr, UWord, U(32), Ptr)]
        #[on(Arm, 276, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Aarch64, 182, I(32), Ptr, UWord, U(32), Ptr)]
        MqTimedsend,
        #[on(X86, 418, I(32), Ptr, UWord, U(32), Ptr)]
        #[on(Arm, 418, I(32), Ptr, UWord, U(32), Ptr)]
        MqTimedsendTime64,
        #[on(X86, 278, Ptr)]
        #[on(X86_64, 241, Ptr)]
        #[on(Arm, 275, Ptr)]
        #[on(Aarch64, 181, Ptr)]
        MqUnlink,
        #[on(X86, 163, UWord, UWord, UWord, UWord, UWord)]
        #[on(X86_64, 25, UWord, UWord, UWord, UWord, UWord)]
        #[on(Arm, 163, UWord, UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 216, UWord, UWord, UWord, UWord, UWord)]
        Mremap,
        #[on(X86, 462, UWord, UWord, UWord)]
        #[on(X86_64, 462, UWord, UWord, UWord)]
        #[on(Arm, 462, UWord, UWord, UWord)]
        #[on(Aarch64, 462, UWord, UWord, UWord)]
        Mseal,
        #[on(X86, 402, I(32), I(32), Ptr)]
        #[on(X86_64, 71, I(32), I(32), Ptr)]
        #[on(Arm, 304, I(32), I(32), Ptr)]
        #[on(Aarch64, 187, I(32), I(32), Ptr)]
        Msgctl,
        #[on(X86, 399, I(32), I(32))]
        #[on(X86_64, 68, I(32), I(32))]
        #[on(Arm, 303, I(32), I(32))]
        #[on(Aarch64, 186, I(32), I(32))]
        Msgget,
        #[on(X86, 401, I(32), Ptr, UWord, IWord, I(32))]
        #[on(X86_64, 70, I(32), Ptr, UWord, IWord, I(32))]
        #[on(Arm, 302, I(32), Ptr, UWord, IWord, I(32))]
        #[on(Aarch64, 188, I(32), Ptr, UWord, IWord, I(32))]
        Msgrcv,
        #[on(X86, 400, I(32), Ptr, UWord, I(32))]
        #[on(X86_64, 69, I(32), Ptr, UWord, I(32))]
        #[on(Arm, 301, I(32), Ptr, UWord, I(32))]
        #[on(Aarch64, 189, I(32), Ptr, UWord, I(32))]
        Msgsnd,
        #[on(X86, 144, UWord, UWord, I(32))]
        #[on(X86_64, 26, UWord, UWord, I(32))]
        #[on(Arm, 144, UWord, UWord, I(32))]
        #[on(Aarch64, 227, UWord, UWord, I(32))]
        Msync,
        #[on(X86, 151, UWord, UWord)]
        #[on(X86_64, 150, UWord, UWord)]
        #[on(Arm, 151, UWord, UWord)]
        #[on(Aarch64, 229, UWord, UWord)]
        Munlock,
        #[on(X86, 153)]
        #[on(X86_64, 152)]
        #[on(Arm, 153)]
        #[on(Aarch64, 231)]
        Munlockall,
        #[on(X86, 91, UWord, UWord)]
        #[on(X86_64, 11, UWord, UWord)]
        #[on(Arm, 91, UWord, UWord)]
        #[on(Aarch64, 215, UWord, UWord)]
        Munmap,
        #[on(X86, 341, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(X86_64, 303, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(Arm, 370, I(32), Ptr, Ptr, Ptr, I(32))]
        #[on(Aarch64, 264, I(32), Ptr, Ptr, Ptr, I(32))]
        NameToHandleAt,
        #[on(X86, 162, Ptr, Ptr)]
        #[on(X86_64, 35, Ptr, Ptr)]
        #[on(Arm, 162, Ptr, Ptr)]
        #[on(Aarch64, 101, Ptr, Ptr)]
        Nanosleep,
        #[on(X86_64, 262, I(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 79, I(32), Ptr, Ptr, I(32))]
        Newfstatat,
        #[on(X86, 142, I(32), Ptr, Ptr, Ptr, Ptr)]
        #[on(Arm, 142, I(32), Ptr, Ptr, Ptr, Ptr)]
        _Newselect,
        #[on(X86, 169)]
        #[on(X86_64, 180)]
        #[on(Arm, 169)]
        #[on(Aarch64, 42)]
        Nfsservctl,
        #[on(X86, 34, I(32))]
        #[on(Arm, 34, I(32))]
        Nice,
        #[on(X86, 28, U(32), Ptr)]
        Oldfstat,
        #[on(X86, 84, Ptr, Ptr)]
        Oldlstat,
        #[on(X86, 59, Ptr)]
        Oldolduname,
        #[on(X86, 18, Ptr, Ptr)]
        Oldstat,
        #[on(X86, 109, Ptr)]
        Olduname,
        #[on(X86, 5, Ptr, I(32), U(16))]
        #[on(X86_64, 2, Ptr, I(32), U(16))]
        #[on(Arm, 5, Ptr, I(32), U(16))]
        Open,
        #[on(X86, 295, I(32), Ptr, I(32), U(16))]
        #[on(X86_64, 257, I(32), Ptr, I(32), U(16))]
        #[on(Arm, 322, I(32), Ptr, I(32), U(16))]
        #[on(Aarch64, 56, I(32), Ptr, I(32), U(16))]
        Openat,
        #[on(X86, 437, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 437, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 437, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 437, I(32), Ptr, Ptr, UWord)]
        Openat2,
        #[on(X86, 342, I(32), Ptr, I(32))]
        #[on(X86_64, 304, I(32), Ptr, I(32))]
        #[on(Arm, 371, I(32), Ptr, I(32))]
        #[on(Aarch64, 265, I(32), Ptr, I(32))]
        OpenByHandleAt,
        #[on(X86, 428, I(32), Ptr, U(32))]
        #[on(X86_64, 428, I(32), Ptr, U(32))]
        #[on(Arm, 428, I(32), Ptr, U(32))]
        #[on(Aarch64, 428, I(32), Ptr, U(32))]
        OpenTree,
        #[on(X86, 467, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(X86_64, 467, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Arm, 467, I(32), Ptr, U(32), Ptr, UWord)]
        #[on(Aarch64, 467, I(32), Ptr, U(32), Ptr, UWord)]
        OpenTreeAttr,
        #[on(X86, 29)]
        #[on(X86_64, 34)]
        #[on(Arm, 29)]
        Pause,
        #[on(Arm, 271, IWord, UWord, UWord)]
        PciconfigIobase,
        #[on(Arm, 272, UWord, UWord, UWord, UWord, Ptr)]
        PciconfigRead,
        #[on(Arm, 273, UWord, UWord, UWord, UWord, Ptr)]
        PciconfigWrite,
        #[on(X86, 336, Ptr, I(32), I(32), I(32), UWord)]
        #[on(X86_64, 298, Ptr, I(32), I(32), I(32), UWord)]
        #[on(Arm, 364, Ptr, I(32), I(32), I(32), UWord)]
        #[on(Aarch64, 241, Ptr, I(32), I(32), I(32), UWord)]
        PerfEventOpen,
        #[on(X86, 136, U(32))]
        #[on(X86_64, 135, U(32))]
        #[on(Arm, 136, U(32))]
        #[on(Aarch64, 92, U(32))]
        Personality,
        #[on(X86, 438, I(32), I(32), U(32))]
        #[on(X86_64, 438, I(32), I(32), U(32))]
        #[on(Arm, 438, I(32), I(32), U(32))]
        #[on(Aarch64, 438, I(32), I(32), U(32))]
        PidfdGetfd,
        #[on(X86, 434, I(32), U(32))]
        #[on(X86_64, 434, I(32), U(32))]
        #[on(Arm, 434, I(32), U(32))]
        #[on(Aarch64, 434, I(32), U(32))]
        PidfdOpen,
        #[on(X86, 424, I(32), I(32), Ptr, U(32))]
        #[on(X86_64, 424, I(32), I(32), Ptr, U(32))]
        #[on(Arm, 424, I(32), I(32), Ptr, U(32))]
        #[on(Aarch64, 424, I(32), I(32), Ptr, U(32))]
        PidfdSendSignal,
        #[on(X86, 42, Ptr)]
        #[on(X86_64, 22, Ptr)]
        #[on(Arm, 42, Ptr)]
        Pipe,
        #[on(X86, 331, Ptr, I(32))]
        #[on(X86_64, 293, Ptr, I(32))]
        #[on(Arm, 359, Ptr, I(32))]
        #[on(Aarch64, 59, Ptr, I(32))]
        Pipe2,
        #[on(X86, 217, Ptr, Ptr)]
        #[on(X86_64, 155, Ptr, Ptr)]
        #[on(Arm, 218, Ptr, Ptr)]
        #[on(Aarch64, 41, Ptr, Ptr)]
        PivotRoot,
        #[on(X86, 381, UWord, UWord)]
        #[on(X86_64, 330, UWord, UWord)]
        #[on(Arm, 395, UWord, UWord)]
        #[on(Aarch64, 289, UWord, UWord)]
        PkeyAlloc,
        #[on(X86, 382, I(32))]
        #[on(X86_64, 331, I(32))]
        #[on(Arm, 396, I(32))]
        #[on(Aarch64, 290, I(32))]
        PkeyFree,
        #[on(X86, 380, UWord, UWord, UWord, I(32))]
        #[on(X86_64, 329, UWord, UWord, UWord, I(32))]
        #[on(Arm, 394, UWord, UWord, UWord, I(32))]
        #[on(Aarch64, 288, UWord, UWord, UWord, I(32))]
        PkeyMprotect,
        #[on(X86, 168, Ptr, U(32), I(32))]
        #[on(X86_64, 7, Ptr, U(32), I(32))]
        #[on(Arm, 168, Ptr, U(32), I(32))]
        Poll,
        #[on(X86, 309, Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 271, Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Arm, 336, Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 73, Ptr, U(32), Ptr, Ptr, UWord)]
        Ppoll,
        #[on(X86, 414, Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Arm, 414, Ptr, U(32), Ptr, Ptr, UWord)]
        PpollTime64,
        #[on(X86, 172, I(32), UWord, UWord, UWord, UWord)]
        #[on(X86_64, 157, I(32), UWord, UWord, UWord, UWord)]
        #[on(Arm, 172, I(32), UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 167, I(32), UWord, UWord, UWord, UWord)]
        Prctl,
        #[on(X86, 180, U(32), Ptr, UWord, I(64))]
        #[on(X86_64, 17, U(32), Ptr, UWord, I(64))]
        #[on(Arm, 180, U(32), Ptr, UWord, I(64))]
        #[on(Aarch64, 67, U(32), Ptr, UWord, I(64))]
        Pread64,
        #[on(X86, 333, UWord, Ptr, UWord, UWord, UWord)]
        #[on(X86_64, 295, UWord, Ptr, UWord, UWord, UWord)]
        #[on(Arm, 361, UWord, Ptr, UWord, UWord, UWord)]
        #[on(Aarch64, 69, UWord, Ptr, UWord, UWord, UWord)]
        Preadv,
        #[on(X86, 378, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(X86_64, 327, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(Arm, 392, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(Aarch64, 286, UWord, Ptr, UWord, UWord, UWord, I(32))]
        Preadv2,
        #[on(X86, 340, I(32), U(32), Ptr, Ptr)]
        #[on(X86_64, 302, I(32), U(32), Ptr, Ptr)]
        #[on(Arm, 369, I(32), U(32), Ptr, Ptr)]
        #[on(Aarch64, 261, I(32), U(32), Ptr, Ptr)]
        Prlimit64,
        #[on(X86, 440, I(32), Ptr, UWord, I(32), U(32))]
        #[on(X86_64, 440, I(32), Ptr, UWord, I(32), U(32))]
        #[on(Arm, 440, I(32), Ptr, UWord, I(32), U(32))]
        #[on(Aarch64, 440, I(32), Ptr, UWord, I(32), U(32))]
        ProcessMadvise,
        #[on(X86, 448, I(32), U(32))]
        #[on(X86_64, 448, I(32), U(32))]
        #[on(Arm, 448, I(32), U(32))]
        #[on(Aarch64, 448, I(32), U(32))]
        ProcessMrelease,
        #[on(X86, 347, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(X86_64, 310, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(Arm, 376, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(Aarch64, 270, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        ProcessVmReadv,
        #[on(X86, 348, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(X86_64, 311, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(Arm, 377, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        #[on(Aarch64, 271, I(32), Ptr, UWord, Ptr, UWord, UWord)]
        ProcessVmWritev,
        #[on(X86, 44)]
        Prof,
        #[on(X86, 98)]
        Profil,
        #[on(X86, 308, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        #[on(X86_64, 270, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        #[on(Arm, 335, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        #[on(Aarch64, 72, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        Pselect6,
        #[on(X86, 413, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        #[on(Arm, 413, I(32), Ptr, Ptr, Ptr, Ptr, Ptr)]
        Pselect6Time64,
        #[on(X86, 26, IWord, IWord, UWord, UWord)]
        #[on(X86_64, 101, IWord, IWord, UWord, UWord)]
        #[on(Arm, 26, IWord, IWord, UWord, UWord)]
        #[on(Aarch64, 117, IWord, IWord, UWord, UWord)]
        Ptrace,
        #[on(X86, 189)]
        #[on(X86_64, 182)]
        Putpmsg,
        #[on(X86, 181, U(32), Ptr, UWord, I(64))]
        #[on(X86_64, 18, U(32), Ptr, UWord, I(64))]
        #[on(Arm, 181, U(32), Ptr, UWord, I(64))]
        #[on(Aarch64, 68, U(32), Ptr, UWord, I(64))]
        Pwrite64,
        #[on(X86, 334, UWord, Ptr, UWord, UWord, UWord)]
        #[on(X86_64, 296, UWord, Ptr, UWord, UWord, UWord)]
        #[on(Arm, 362, UWord, Ptr, UWord, UWord, UWord)]
        #[on(Aarch64, 70, UWord, Ptr, UWord, UWord, UWord)]
        Pwritev,
        #[on(X86, 379, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(X86_64, 328, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(Arm, 393, UWord, Ptr, UWord, UWord, UWord, I(32))]
        #[on(Aarch64, 287, UWord, Ptr, UWord, UWord, UWord, I(32))]
        Pwritev2,
        #[on(X86, 167)]
        #[on(X86_64, 178)]
        QueryModule,
        #[on(X86, 131, U(32), Ptr, U(32), Ptr)]
        #[on(X86_64, 179, U(32), Ptr, U(32), Ptr)]
        #[on(Arm, 131, U(32), Ptr, U(32), Ptr)]
        #[on(Aarch64, 60, U(32), Ptr, U(32), Ptr)]
        Quotactl,
        #[on(X86, 443, U(32), U(32), U(32), Ptr)]
        #[on(X86_64, 443, U(32), U(32), U(32), Ptr)]
        #[on(Arm, 443, U(32), U(32), U(32), Ptr)]
        #[on(Aarch64, 443, U(32), U(32), U(32), Ptr)]
        QuotactlFd,
        #[on(X86, 3, U(32), Ptr, UWord)]
        #[on(X86_64, 0, U(32), Ptr, UWord)]
        #[on(Arm, 3, U(32), Ptr, UWord)]
        #[on(Aarch64, 63, U(32), Ptr, UWord)]
        Read,
        #[on(X86, 225, I(32), I(64), UWord)]
        #[on(X86_64, 187, I(32), I(64), UWord)]
        #[on(Arm, 225, I(32), I(64), UWord)]
        #[on(Aarch64, 213, I(32), I(64), UWord)]
        Readahead,
        #[on(X86, 89, U(32), Ptr, U(32))]
        Readdir,
        #[on(X86, 85, Ptr, Ptr, I(32))]
        #[on(X86_64, 89, Ptr, Ptr, I(32))]
        #[on(Arm, 85, Ptr, Ptr, I(32))]
        Readlink,
        #[on(X86, 305, I(32), Ptr, Ptr, I(32))]
        #[on(X86_64, 267, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 332, I(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 78, I(32), Ptr, Ptr, I(32))]
        Readlinkat,
        #[on(X86, 145, UWord, Ptr, UWord)]
        #[on(X86_64, 19, UWord, Ptr, UWord)]
        #[on(Arm, 145, UWord, Ptr, UWord)]
        #[on(Aarch64, 65, UWord, Ptr, UWord)]
        Readv,
        #[on(X86, 88, I(32), I(32), U(32), Ptr)]
        #[on(X86_64, 169, I(32), I(32), U(32), Ptr)]
        #[on(Arm, 88, I(32), I(32), U(32), Ptr)]
        #[on(Aarch64, 142, I(32), I(32), U(32), Ptr)]
        Reboot,
        #[on(Arm, 291, I(32), Ptr, UWord, U(32))]
        Recv,
        #[on(X86, 371, I(32), Ptr, UWord, U(32), Ptr, Ptr)]
        #[on(X86_64, 45, I(32), Ptr, UWord, U(32), Ptr, Ptr)]
        #[on(Arm, 292, I(32), Ptr, UWord, U(32), Ptr, Ptr)]
        #[on(Aarch64, 207, I(32), Ptr, UWord, U(32), Ptr, Ptr)]
        Recvfrom,
        #[on(X86, 337, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(X86_64, 299, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Arm, 365, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Aarch64, 243, I(32), Ptr, U(32), U(32), Ptr)]
        Recvmmsg,
        #[on(X86, 417, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Arm, 417, I(32), Ptr, U(32), U(32), Ptr)]
        RecvmmsgTime64,
        #[on(X86, 372, I(32), Ptr, U(32))]
        #[on(X86_64, 47, I(32), Ptr, U(32))]
        #[on(Arm, 297, I(32), Ptr, U(32))]
        #[on(Aarch64, 212, I(32), Ptr, U(32))]
        Recvmsg,
        #[on(X86, 257, UWord, UWord, UWord, UWord, UWord)]
        #[on(X86_64, 216, UWord, UWord, UWord, UWord, UWord)]
        #[on(Arm, 253, UWord, UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 234, UWord, UWord, UWord, UWord, UWord)]
        RemapFilePages,
        #[on(X86, 235, Ptr, Ptr)]
        #[on(X86_64, 197, Ptr, Ptr)]
        #[on(Arm, 235, Ptr, Ptr)]
        #[on(Aarch64, 14, Ptr, Ptr)]
        Removexattr,
        #[on(X86, 466, I(32), Ptr, U(32), Ptr)]
        #[on(X86_64, 466, I(32), Ptr, U(32), Ptr)]
        #[on(Arm, 466, I(32), Ptr, U(32), Ptr)]
        #[on(Aarch64, 466, I(32), Ptr, U(32), Ptr)]
        Removexattrat,
        #[on(X86, 38, Ptr, Ptr)]
        #[on(X86_64, 82, Ptr, Ptr)]
        #[on(Arm, 38, Ptr, Ptr)]
        Rename,
        #[on(X86, 302, I(32), Ptr, I(32), Ptr)]
        #[on(X86_64, 264, I(32), Ptr, I(32), Ptr)]
        #[on(Arm, 329, I(32), Ptr, I(32), Ptr)]
        #[on(Aarch64, 38, I(32), Ptr, I(32), Ptr)]
        Renameat,
        #[on(X86, 353, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(X86_64, 316, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(Arm, 382, I(32), Ptr, I(32), Ptr, U(32))]
        #[on(Aarch64, 276, I(32), Ptr, I(32), Ptr, U(32))]
        Renameat2,
        #[on(X86, 287, Ptr, Ptr, Ptr, I(32))]
        #[on(X86_64, 249, Ptr, Ptr, Ptr, I(32))]
        #[on(Arm, 310, Ptr, Ptr, Ptr, I(32))]
        #[on(Aarch64, 218, Ptr, Ptr, Ptr, I(32))]
        RequestKey,
        #[on(X86, 0)]
        #[on(X86_64, 219)]
        #[on(Arm, 0)]
        #[on(Aarch64, 128)]
        RestartSyscall,
        #[on(X86, 40, Ptr)]
        #[on(X86_64, 84, Ptr)]
        #[on(Arm, 40, Ptr)]
        Rmdir,
        #[on(X86, 386, Ptr, U(32), I(32), U(32))]
        #[on(X86_64, 334, Ptr, U(32), I(32), U(32))]
        #[on(Arm, 398, Ptr, U(32), I(32), U(32))]
        #[on(Aarch64, 293, Ptr, U(32), I(32), U(32))]
        Rseq,
        #[on(X86, 471)]
        #[on(X86_64, 471)]
        #[on(Arm, 471)]
        #[on(Aarch64, 471)]
        RseqSliceYield,
        #[on(X86, 174, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 13, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 174, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 134, I(32), Ptr, Ptr, UWord)]
        RtSigaction,
        #[on(X86, 176, Ptr, UWord)]
        #[on(X86_64, 127, Ptr, UWord)]
        #[on(Arm, 176, Ptr, UWord)]
        #[on(Aarch64, 136, Ptr, UWord)]
        RtSigpending,
        #[on(X86, 175, I(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 14, I(32), Ptr, Ptr, UWord)]
        #[on(Arm, 175, I(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 135, I(32), Ptr, Ptr, UWord)]
        RtSigprocmask,
        #[on(X86, 178, I(32), I(32), Ptr)]
        #[on(X86_64, 129, I(32), I(32), Ptr)]
        #[on(Arm, 178, I(32), I(32), Ptr)]
        #[on(Aarch64, 138, I(32), I(32), Ptr)]
        RtSigqueueinfo,
        #[on(X86, 173)]
        #[on(X86_64, 15)]
        #[on(Arm, 173)]
        #[on(Aarch64, 139)]
        RtSigreturn,
        #[on(X86, 179, Ptr, UWord)]
        #[on(X86_64, 130, Ptr, UWord)]
        #[on(Arm, 179, Ptr, UWord)]
        #[on(Aarch64, 133, Ptr, UWord)]
        RtSigsuspend,
        #[on(X86, 177, Ptr, Ptr, Ptr, UWord)]
        #[on(X86_64, 128, Ptr, Ptr, Ptr, UWord)]
        #[on(Arm, 177, Ptr, Ptr, Ptr, UWord)]
        #[on(Aarch64, 137, Ptr, Ptr, Ptr, UWord)]
        RtSigtimedwait,
        #[on(X86, 421, Ptr, Ptr, Ptr, UWord)]
        #[on(Arm, 421, Ptr, Ptr, Ptr, UWord)]
        RtSigtimedwaitTime64,
        #[on(X86, 335, I(32), I(32), I(32), Ptr)]
        #[on(X86_64, 297, I(32), I(32), I(32), Ptr)]
        #[on(Arm, 363, I(32), I(32), I(32), Ptr)]
        #[on(Aarch64, 240, I(32), I(32), I(32), Ptr)]
        RtTgsigqueueinfo,
        #[on(X86, 242, I(32), U(32), Ptr)]
        #[on(X86_64, 204, I(32), U(32), Ptr)]
        #[on(Arm, 242, I(32), U(32), Ptr)]
        #[on(Aarch64, 123, I(32), U(32), Ptr)]
        SchedGetaffinity,
        #[on(X86, 352, I(32), Ptr, U(32), U(32))]
        #[on(X86_64, 315, I(32), Ptr, U(32), U(32))]
        #[on(Arm, 381, I(32), Ptr, U(32), U(32))]
        #[on(Aarch64, 275, I(32), Ptr, U(32), U(32))]
        SchedGetattr,
        #[on(X86, 155, I(32), Ptr)]
        #[on(X86_64, 143, I(32), Ptr)]
        #[on(Arm, 155, I(32), Ptr)]
        #[on(Aarch64, 121, I(32), Ptr)]
        SchedGetparam,
        #[on(X86, 159, I(32))]
        #[on(X86_64, 146, I(32))]
        #[on(Arm, 159, I(32))]
        #[on(Aarch64, 125, I(32))]
        SchedGetPriorityMax,
        #[on(X86, 160, I(32))]
        #[on(X86_64, 147, I(32))]
        #[on(Arm, 160, I(32))]
        #[on(Aarch64, 126, I(32))]
        SchedGetPriorityMin,
        #[on(X86, 157, I(32))]
        #[on(X86_64, 145, I(32))]
        #[on(Arm, 157, I(32))]
        #[on(Aarch64, 120, I(32))]
        SchedGetscheduler,
        #[on(X86, 161, I(32), Ptr)]
        #[on(X86_64, 148, I(32), Ptr)]
        #[on(Arm, 161, I(32), Ptr)]
        #[on(Aarch64, 127, I(32), Ptr)]
        SchedRrGetInterval,
        #[on(X86, 423, I(32), Ptr)]
        #[on(Arm, 423, I(32), Ptr)]
        SchedRrGetIntervalTime64,
        #[on(X86, 241, I(32), U(32), Ptr)]
        #[on(X86_64, 203, I(32), U(32), Ptr)]
        #[on(Arm, 241, I(32), U(32), Ptr)]
        #[on(Aarch64, 122, I(32), U(32), Ptr)]
        SchedSetaffinity,
        #[on(X86, 351, I(32), Ptr, U(32))]
        #[on(X86_64, 314, I(32), Ptr, U(32))]
        #[on(Arm, 380, I(32), Ptr, U(32))]
        #[on(Aarch64, 274, I(32), Ptr, U(32))]
        SchedSetattr,
        #[on(X86, 154, I(32), Ptr)]
        #[on(X86_64, 142, I(32), Ptr)]
        #[on(Arm, 154, I(32), Ptr)]
        #[on(Aarch64, 118, I(32), Ptr)]
        SchedSetparam,
        #[on(X86, 156, I(32), I(32), Ptr)]
        #[on(X86_64, 144, I(32), I(32), Ptr)]
        #[on(Arm, 156, I(32), I(32), Ptr)]
        #[on(Aarch64, 119, I(32), I(32), Ptr)]
        SchedSetscheduler,
        #[on(X86, 158)]
        #[on(X86_64, 24)]
        #[on(Arm, 158)]
        #[on(Aarch64, 124)]
        SchedYield,
        #[on(X86, 354, U(32), U(32), Ptr)]
        #[on(X86_64, 317, U(32), U(32), Ptr)]
        #[on(Arm, 383, U(32), U(32), Ptr)]
        #[on(Aarch64, 277, U(32), U(32), Ptr)]
        Seccomp,
        #[on(X86_64, 185)]
        Security,
        #[on(X86, 82, Ptr)]
        #[on(X86_64, 23, I(32), Ptr, Ptr, Ptr, Ptr)]
        Select,
        #[on(X86, 394, I(32), I(32), I(32), UWord)]
        #[on(X86_64, 66, I(32), I(32), I(32), UWord)]
        #[on(Arm, 300, I(32), I(32), I(32), UWord)]
        #[on(Aarch64, 191, I(32), I(32), I(32), UWord)]
        Semctl,
        #[on(X86, 393, I(32), I(32), I(32))]
        #[on(X86_64, 64, I(32), I(32), I(32))]
        #[on(Arm, 299, I(32), I(32), I(32))]
        #[on(Aarch64, 190, I(32), I(32), I(32))]
        Semget,
        #[on(X86_64, 65, I(32), Ptr, U(32))]
        #[on(Arm, 298, I(32), Ptr, U(32))]
        #[on(Aarch64, 193, I(32), Ptr, U(32))]
        Semop,
        #[on(X86_64, 220, I(32), Ptr, U(32), Ptr)]
        #[on(Arm, 312, I(32), Ptr, U(32), Ptr)]
        #[on(Aarch64, 192, I(32), Ptr, U(32), Ptr)]
        Semtimedop,
        #[on(X86, 420, I(32), Ptr, U(32), Ptr)]
        #[on(Arm, 420, I(32), Ptr, U(32), Ptr)]
        SemtimedopTime64,
        #[on(Arm, 289, I(32), Ptr, UWord, U(32))]
        Send,
        #[on(X86, 187, I(32), I(32), Ptr, UWord)]
        #[on(X86_64, 40, I(32), I(32), Ptr, UWord)]
        #[on(Arm, 187, I(32), I(32), Ptr, UWord)]
        #[on(Aarch64, 71, I(32), I(32), Ptr, UWord)]
        Sendfile,
        #[on(X86, 239, I(32), I(32), Ptr, UWord)]
        #[on(Arm, 239, I(32), I(32), Ptr, UWord)]
        Sendfile64,
        #[on(X86, 345, I(32), Ptr, U(32), U(32))]
        #[on(X86_64, 307, I(32), Ptr, U(32), U(32))]
        #[on(Arm, 374, I(32), Ptr, U(32), U(32))]
        #[on(Aarch64, 269, I(32), Ptr, U(32), U(32))]
        Sendmmsg,
        #[on(X86, 370, I(32), Ptr, U(32))]
        #[on(X86_64, 46, I(32), Ptr, U(32))]
        #[on(Arm, 296, I(32), Ptr, U(32))]
        #[on(Aarch64, 211, I(32), Ptr, U(32))]
        Sendmsg,
        #[on(X86, 369, I(32), Ptr, UWord, U(32), Ptr, I(32))]
        #[on(X86_64, 44, I(32), Ptr, UWord, U(32), Ptr, I(32))]
        #[on(Arm, 290, I(32), Ptr, UWord, U(32), Ptr, I(32))]
        #[on(Aarch64, 206, I(32), Ptr, UWord, U(32), Ptr, I(32))]
        Sendto,
        #[on(X86, 121, Ptr, I(32))]
        #[on(X86_64, 171, Ptr, I(32))]
        #[on(Arm, 121, Ptr, I(32))]
        #[on(Aarch64, 162, Ptr, I(32))]
        Setdomainname,
        #[on(X86, 139, U(16))]
        #[on(X86_64, 123, U(32))]
        #[on(Arm, 139, U(16))]
        #[on(Aarch64, 152, U(32))]
        Setfsgid,
        #[on(X86, 216, U(32))]
        #[on(Arm, 216, U(32))]
        Setfsgid32,
        #[on(X86, 138, U(16))]
        #[on(X86_64, 122, U(32))]
        #[on(Arm, 138, U(16))]
        #[on(Aarch64, 151, U(32))]
        Setfsuid,
        #[on(X86, 215, U(32))]
        #[on(Arm, 215, U(32))]
        Setfsuid32,
        #[on(X86, 46, U(16))]
        #[on(X86_64, 106, U(32))]
        #[on(Arm, 46, U(16))]
        #[on(Aarch64, 144, U(32))]
        Setgid,
        #[on(X86, 214, U(32))]
        #[on(Arm, 214, U(32))]
        Setgid32,
        #[on(X86, 81, I(32), Ptr)]
        #[on(X86_64, 116, I(32), Ptr)]
        #[on(Arm, 81, I(32), Ptr)]
        #[on(Aarch64, 159, I(32), Ptr)]
        Setgroups,
        #[on(X86, 206, I(32), Ptr)]
        #[on(Arm, 206, I(32), Ptr)]
        Setgroups32,
        #[on(X86, 74, Ptr, I(32))]
        #[on(X86_64, 170, Ptr, I(32))]
        #[on(Arm, 74, Ptr, I(32))]
        #[on(Aarch64, 161, Ptr, I(32))]
        Sethostname,
        #[on(X86, 104, I(32), Ptr, Ptr)]
        #[on(X86_64, 38, I(32), Ptr, Ptr)]
        #[on(Arm, 104, I(32), Ptr, Ptr)]
        #[on(Aarch64, 103, I(32), Ptr, Ptr)]
        Setitimer,
        #[on(X86, 276, I(32), Ptr, UWord)]
        #[on(X86_64, 238, I(32), Ptr, UWord)]
        #[on(Arm, 321, I(32), Ptr, UWord)]
        #[on(Aarch64, 237, I(32), Ptr, UWord)]
        SetMempolicy,
        #[on(X86, 450, UWord, UWord, UWord, UWord)]
        #[on(X86_64, 450, UWord, UWord, UWord, UWord)]
        #[on(Arm, 450, UWord, UWord, UWord, UWord)]
        #[on(Aarch64, 450, UWord, UWord, UWord, UWord)]
        SetMempolicyHomeNode,
        #[on(X86, 346, I(32), I(32))]
        #[on(X86_64, 308, I(32), I(32))]
        #[on(Arm, 375, I(32), I(32))]
        #[on(Aarch64, 268, I(32), I(32))]
        Setns,
        #[on(X86, 57, I(32), I(32))]
        #[on(X86_64, 109, I(32), I(32))]
        #[on(Arm, 57, I(32), I(32))]
        #[on(Aarch64, 154, I(32), I(32))]
        Setpgid,
        #[on(X86, 97, I(32), I(32), I(32))]
        #[on(X86_64, 141, I(32), I(32), I(32))]
        #[on(Arm, 97, I(32), I(32), I(32))]
        #[on(Aarch64, 140, I(32), I(32), I(32))]
        Setpriority,
        #[on(X86, 71, U(16), U(16))]
        #[on(X86_64, 114, U(32), U(32))]
        #[on(Arm, 71, U(16), U(16))]
        #[on(Aarch64, 143, U(32), U(32))]
        Setregid,
        #[on(X86, 204, U(32), U(32))]
        #[on(Arm, 204, U(32), U(32))]
        Setregid32,
        #[on(X86, 170, U(16), U(16), U(16))]
        #[on(X86_64, 119, U(32), U(32), U(32))]
        #[on(Arm, 170, U(16), U(16), U(16))]
        #[on(Aarch64, 149, U(32), U(32), U(32))]
        Setresgid,
        #[on(X86, 210, U(32), U(32), U(32))]
        #[on(Arm, 210, U(32), U(32), U(32))]
        Setresgid32,
        #[on(X86, 164, U(16), U(16), U(16))]
        #[on(X86_64, 117, U(32), U(32), U(32))]
        #[on(Arm, 164, U(16), U(16), U(16))]
        #[on(Aarch64, 147, U(32), U(32), U(32))]
        Setresuid,
        #[on(X86, 208, U(32), U(32), U(32))]
        #[on(Arm, 208, U(32), U(32), U(32))]
        Setresuid32,
        #[on(X86, 70, U(16), U(16))]
        #[on(X86_64, 113, U(32), U(32))]
        #[on(Arm, 70, U(16), U(16))]
        #[on(Aarch64, 145, U(32), U(32))]
        Setreuid,
        #[on(X86, 203, U(32), U(32))]
        #[on(Arm, 203, U(32), U(32))]
        Setreuid32,
        #[on(X86, 75, U(32), Ptr)]
        #[on(X86_64, 160, U(32), Ptr)]
        #[on(Arm, 75, U(32), Ptr)]
        #[on(Aarch64, 164, U(32), Ptr)]
        Setrlimit,
        #[on(X86, 311, Ptr, UWord)]
        #[on(X86_64, 273, Ptr, UWord)]
        #[on(Arm, 338, Ptr, UWord)]
        #[on(Aarch64, 99, Ptr, UWord)]
        SetRobustList,
        #[on(X86, 66)]
        #[on(X86_64, 112)]
        #[on(Arm, 66)]
        #[on(Aarch64, 157)]
        Setsid,
        #[on(X86, 366, I(32), I(32), I(32), Ptr, I(32))]
        #[on(X86_64, 54, I(32), I(32), I(32), Ptr, I(32))]
        #[on(Arm, 294, I(32), I(32), I(32), Ptr, I(32))]
        #[on(Aarch64, 208, I(32), I(32), I(32), Ptr, I(32))]
        Setsockopt,
        #[on(X86, 243, Ptr)]
        #[on(X86_64, 205)]
        SetThreadArea,
        #[on(X86, 258, Ptr)]
        #[on(X86_64, 218, Ptr)]
        #[on(Arm, 256, Ptr)]
        #[on(Aarch64, 96, Ptr)]
        SetTidAddress,
        #[on(X86, 79, Ptr, Ptr)]
        #[on(X86_64, 164, Ptr, Ptr)]
        #[on(Arm, 79, Ptr, Ptr)]
        #[on(Aarch64, 170, Ptr, Ptr)]
        Settimeofday,
        #[on(Arm, 983045, UWord)]
        SetTls,
        #[on(X86, 23, U(16))]
        #[on(X86_64, 105, U(32))]
        #[on(Arm, 23, U(16))]
        #[on(Aarch64, 146, U(32))]
        Setuid,
        #[on(X86, 213, U(32))]
        #[on(Arm, 213, U(32))]
        Setuid32,
        #[on(X86, 226, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(X86_64, 188, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Arm, 226, Ptr, Ptr, Ptr, UWord, I(32))]
        #[on(Aarch64, 5, Ptr, Ptr, Ptr, UWord, I(32))]
        Setxattr,
        #[on(X86, 463, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(X86_64, 463, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Arm, 463, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        #[on(Aarch64, 463, I(32), Ptr, U(32), Ptr, Ptr, UWord)]
        Setxattrat,
        #[on(X86, 68)]
        Sgetmask,
        #[on(X86, 397, I(32), Ptr, I(32))]
        #[on(X86_64, 30, I(32), Ptr, I(32))]
        #[on(Arm, 305, I(32), Ptr, I(32))]
        #[on(Aarch64, 196, I(32), Ptr, I(32))]
        Shmat,
        #[on(X86, 396, I(32), I(32), Ptr)]
        #[on(X86_64, 31, I(32), I(32), Ptr)]
        #[on(Arm, 308, I(32), I(32), Ptr)]
        #[on(Aarch64, 195, I(32), I(32), Ptr)]
        Shmctl,
        #[on(X86, 398, Ptr)]
        #[on(X86_64, 67, Ptr)]
        #[on(Arm, 306, Ptr)]
        #[on(Aarch64, 197, Ptr)]
        Shmdt,
        #[on(X86, 395, I(32), UWord, I(32))]
        #[on(X86_64, 29, I(32), UWord, I(32))]
        #[on(Arm, 307, I(32), UWord, I(32))]
        #[on(Aarch64, 194, I(32), UWord, I(32))]
        Shmget,
        #[on(X86, 373, I(32), I(32))]
        #[on(X86_64, 48, I(32), I(32))]
        #[on(Arm, 293, I(32), I(32))]
        #[on(Aarch64, 210, I(32), I(32))]
        Shutdown,
        #[on(X86, 67, I(32), Ptr, Ptr)]
        #[on(Arm, 67, I(32), Ptr, Ptr)]
        Sigaction,
        #[on(X86, 186, Ptr, Ptr)]
        #[on(X86_64, 131, Ptr, Ptr)]
        #[on(Arm, 186, Ptr, Ptr)]
        #[on(Aarch64, 132, Ptr, Ptr)]
        Sigaltstack,
        #[on(X86, 48, I(32), Ptr)]
        Signal,
        #[on(X86, 321, I(32), Ptr, UWord)]
        #[on(X86_64, 282, I(32), Ptr, UWord)]
        #[on(Arm, 349, I(32), Ptr, UWord)]
        Signalfd,
        #[on(X86, 327, I(32), Ptr, UWord, I(32))]
        #[on(X86_64, 289, I(32), Ptr, UWord, I(32))]
        #[on(Arm, 355, I(32), Ptr, UWord, I(32))]
        #[on(Aarch64, 74, I(32), Ptr, UWord, I(32))]
        Signalfd4,
        #[on(X86, 73, Ptr)]
        #[on(Arm, 73, Ptr)]
        Sigpending,
        #[on(X86, 126, I(32), Ptr, Ptr)]
        #[on(Arm, 126, I(32), Ptr, Ptr)]
        Sigprocmask,
        #[on(X86, 119)]
        #[on(Arm, 119)]
        Sigreturn,
        #[on(X86, 72, I(32), I(32), UWord)]
        #[on(Arm, 72, I(32), I(32), UWord)]
        Sigsuspend,
        #[on(X86, 359, I(32), I(32), I(32))]
        #[on(X86_64, 41, I(32), I(32), I(32))]
        #[on(Arm, 281, I(32), I(32), I(32))]
        #[on(Aarch64, 198, I(32), I(32), I(32))]
        Socket,
        #[on(X86, 102, I(32), Ptr)]
        Socketcall,
        #[on(X86, 360, I(32), I(32), I(32), Ptr)]
        #[on(X86_64, 53, I(32), I(32), I(32), Ptr)]
        #[on(Arm, 288, I(32), I(32), I(32), Ptr)]
        #[on(Aarch64, 199, I(32), I(32), I(32), Ptr)]
        Socketpair,
        #[on(X86, 313, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(X86_64, 275, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(Arm, 340, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        #[on(Aarch64, 76, I(32), Ptr, I(32), Ptr, UWord, U(32))]
        Splice,
        #[on(X86, 69, I(32))]
        Ssetmask,
        #[on(X86, 106, Ptr, Ptr)]
        #[on(X86_64, 4, Ptr, Ptr)]
        #[on(Arm, 106, Ptr, Ptr)]
        Stat,
        #[on(X86, 195, Ptr, Ptr)]
        #[on(Arm, 195, Ptr, Ptr)]
        Stat64,
        #[on(X86, 99, Ptr, Ptr)]
        #[on(X86_64, 137, Ptr, Ptr)]
        #[on(Arm, 99, Ptr, Ptr)]
        #[on(Aarch64, 43, Ptr, Ptr)]
        Statfs,
        #[on(X86, 268, Ptr, UWord, Ptr)]
        #[on(Arm, 266, Ptr, UWord, Ptr)]
        Statfs64,
        #[on(X86, 457, Ptr, Ptr, UWord, U(32))]
        #[on(X86_64, 457, Ptr, Ptr, UWord, U(32))]
        #[on(Arm, 457, Ptr, Ptr, UWord, U(32))]
        #[on(Aarch64, 457, Ptr, Ptr, UWord, U(32))]
        Statmount,
        #[on(X86, 383, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(X86_64, 332, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Arm, 397, I(32), Ptr, U(32), U(32), Ptr)]
        #[on(Aarch64, 291, I(32), Ptr, U(32), U(32), Ptr)]
        Statx,
        #[on(X86, 25, Ptr)]
        Stime,
        #[on(X86, 31)]
        Stty,
        #[on(X86, 115, Ptr)]
        #[on(X86_64, 168, Ptr)]
        #[on(Arm, 115, Ptr)]
        #[on(Aarch64, 225, Ptr)]
        Swapoff,
        #[on(X86, 87, Ptr, I(32))]
        #[on(X86_64, 167, Ptr, I(32))]
        #[on(Arm, 87, Ptr, I(32))]
        #[on(Aarch64, 224, Ptr, I(32))]
        Swapon,
        #[on(X86, 83, Ptr, Ptr)]
        #[on(X86_64, 88, Ptr, Ptr)]
        #[on(Arm, 83, Ptr, Ptr)]
        Symlink,
        #[on(X86, 304, Ptr, I(32), Ptr)]
        #[on(X86_64, 266, Ptr, I(32), Ptr)]
        #[on(Arm, 331, Ptr, I(32), Ptr)]
        #[on(Aarch64, 36, Ptr, I(32), Ptr)]
        Symlinkat,
        #[on(X86, 36)]
        #[on(X86_64, 162)]
        #[on(Arm, 36)]
        #[on(Aarch64, 81)]
        Sync,
        #[on(X86, 314, I(32), I(64), I(64), U(32))]
        #[on(X86_64, 277, I(32), I(64), I(64), U(32))]
        #[on(Aarch64, 84, I(32), I(64), I(64), U(32))]
        SyncFileRange,
        #[on(X86, 344, I(32))]
        #[on(X86_64, 306, I(32))]
        #[on(Arm, 373, I(32))]
        #[on(Aarch64, 267, I(32))]
        Syncfs,
        #[on(X86, 149)]
        #[on(X86_64, 156)]
        #[on(Arm, 149)]
        _Sysctl,
        #[on(X86, 135, I(32), UWord, UWord)]
        #[on(X86_64, 139, I(32), UWord, UWord)]
        #[on(Arm, 135, I(32), UWord, UWord)]
        Sysfs,
        #[on(X86, 116, Ptr)]
        #[on(X86_64, 99, Ptr)]
        #[on(Arm, 116, Ptr)]
        #[on(Aarch64, 179, Ptr)]
        Sysinfo,
        #[on(X86, 103, I(32), Ptr, I(32))]
        #[on(X86_64, 103, I(32), Ptr, I(32))]
        #[on(Arm, 103, I(32), Ptr, I(32))]
        #[on(Aarch64, 116, I(32), Ptr, I(32))]
        Syslog,
        #[on(X86, 315, I(32), I(32), UWord, U(32))]
        #[on(X86_64, 276, I(32), I(32), UWord, U(32))]
        #[on(Arm, 342, I(32), I(32), UWord, U(32))]
        #[on(Aarch64, 77, I(32), I(32), UWord, U(32))]
        Tee,
        #[on(X86, 270, I(32), I(32), I(32))]
        #[on(X86_64, 234, I(32), I(32), I(32))]
        #[on(Arm, 268, I(32), I(32), I(32))]
        #[on(Aarch64, 131, I(32), I(32), I(32))]
        Tgkill,
        #[on(X86, 13, Ptr)]
        #[on(X86_64, 201, Ptr)]
        Time,
        #[on(X86, 259, I(32), Ptr, Ptr)]
        #[on(X86_64, 222, I(32), Ptr, Ptr)]
        #[on(Arm, 257, I(32), Ptr, Ptr)]
        #[on(Aarch64, 107, I(32), Ptr, Ptr)]
        TimerCreate,
        #[on(X86, 263, I(32))]
        #[on(X86_64, 226, I(32))]
        #[on(Arm, 261, I(32))]
        #[on(Aarch64, 111, I(32))]
        TimerDelete,
        #[on(X86, 322, I(32), I(32))]
        #[on(X86_64, 283, I(32), I(32))]
        #[on(Arm, 350, I(32), I(32))]
        #[on(Aarch64, 85, I(32), I(32))]
        TimerfdCreate,
        #[on(X86, 326, I(32), Ptr)]
        #[on(X86_64, 287, I(32), Ptr)]
        #[on(Arm, 354, I(32), Ptr)]
        #[on(Aarch64, 87, I(32), Ptr)]
        TimerfdGettime,
        #[on(X86, 410, I(32), Ptr)]
        #[on(Arm, 410, I(32), Ptr)]
        TimerfdGettime64,
        #[on(X86, 325, I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 286, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 353, I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 86, I(32), I(32), Ptr, Ptr)]
        TimerfdSettime,
        #[on(X86, 411, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 411, I(32), I(32), Ptr, Ptr)]
        TimerfdSettime64,
        #[on(X86, 262, I(32))]
        #[on(X86_64, 225, I(32))]
        #[on(Arm, 260, I(32))]
        #[on(Aarch64, 109, I(32))]
        TimerGetoverrun,
        #[on(X86, 261, I(32), Ptr)]
        #[on(X86_64, 224, I(32), Ptr)]
        #[on(Arm, 259, I(32), Ptr)]
        #[on(Aarch64, 108, I(32), Ptr)]
        TimerGettime,
        #[on(X86, 408, I(32), Ptr)]
        #[on(Arm, 408, I(32), Ptr)]
        TimerGettime64,
        #[on(X86, 260, I(32), I(32), Ptr, Ptr)]
        #[on(X86_64, 223, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 258, I(32), I(32), Ptr, Ptr)]
        #[on(Aarch64, 110, I(32), I(32), Ptr, Ptr)]
        TimerSettime,
        #[on(X86, 409, I(32), I(32), Ptr, Ptr)]
        #[on(Arm, 409, I(32), I(32), Ptr, Ptr)]
        TimerSettime64,
        #[on(X86, 43, Ptr)]
        #[on(X86_64, 100, Ptr)]
        #[on(Arm, 43, Ptr)]
        #[on(Aarch64, 153, Ptr)]
        Times,
        #[on(X86, 238, I(32), I(32))]
        #[on(X86_64, 200, I(32), I(32))]
        #[on(Arm, 238, I(32), I(32))]
        #[on(Aarch64, 130, I(32), I(32))]
        Tkill,
        #[on(X86, 92, Ptr, IWord)]
        #[on(X86_64, 76, Ptr, IWord)]
        #[on(Arm, 92, Ptr, IWord)]
        #[on(Aarch64, 45, Ptr, IWord)]
        Truncate,
        #[on(X86, 193, Ptr, I(64))]
        #[on(Arm, 193, Ptr, I(64))]
        Truncate64,
        #[on(X86_64, 184)]
        Tuxcall,
        #[on(X86, 191, U(32), Ptr)]
        #[on(Arm, 191, U(32), Ptr)]
        Ugetrlimit,
        #[on(X86, 58)]
        Ulimit,
        #[on(X86, 60, I(32))]
        #[on(X86_64, 95, I(32))]
        #[on(Arm, 60, I(32))]
        #[on(Aarch64, 166, I(32))]
        Umask,
        #[on(X86, 22, Ptr)]
        Umount,
        #[on(X86, 52, Ptr, I(32))]
        #[on(X86_64, 166, Ptr, I(32))]
        #[on(Arm, 52, Ptr, I(32))]
        #[on(Aarch64, 39, Ptr, I(32))]
        Umount2,
        #[on(X86, 122, Ptr)]
        #[on(X86_64, 63, Ptr)]
        #[on(Arm, 122, Ptr)]
        #[on(Aarch64, 160, Ptr)]
        Uname,
        #[on(X86, 10, Ptr)]
        #[on(X86_64, 87, Ptr)]
        #[on(Arm, 10, Ptr)]
        Unlink,
        #[on(X86, 301, I(32), Ptr, I(32))]
        #[on(X86_64, 263, I(32), Ptr, I(32))]
        #[on(Arm, 328, I(32), Ptr, I(32))]
        #[on(Aarch64, 35, I(32), Ptr, I(32))]
        Unlinkat,
        #[on(X86, 310, UWord)]
        #[on(X86_64, 272, UWord)]
        #[on(Arm, 337, UWord)]
        #[on(Aarch64, 97, UWord)]
        Unshare,
        #[on(X86_64, 336)]
        Uprobe,
        #[on(X86_64, 335)]
        Uretprobe,
        #[on(X86, 86, Ptr)]
        #[on(X86_64, 134)]
        #[on(Arm, 86, Ptr)]
        Uselib,
        #[on(X86, 374, I(32))]
        #[on(X86_64, 323, I(32))]
        #[on(Arm, 388, I(32))]
        #[on(Aarch64, 282, I(32))]
        Userfaultfd,
        #[on(Arm, 983043)]
        Usr26,
        #[on(Arm, 983044)]
        Usr32,
        #[on(X86, 62, U(32), Ptr)]
        #[on(X86_64, 136, U(32), Ptr)]
        #[on(Arm, 62, U(32), Ptr)]
        Ustat,
        #[on(X86, 30, Ptr, Ptr)]
        #[on(X86_64, 132, Ptr, Ptr)]
        Utime,
        #[on(X86, 320, U(32), Ptr, Ptr, I(32))]
        #[on(X86_64, 280, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 348, U(32), Ptr, Ptr, I(32))]
        #[on(Aarch64, 88, I(32), Ptr, Ptr, I(32))]
        Utimensat,
        #[on(X86, 412, I(32), Ptr, Ptr, I(32))]
        #[on(Arm, 412, I(32), Ptr, Ptr, I(32))]
        UtimensatTime64,
        #[on(X86, 271, Ptr, Ptr)]
        #[on(X86_64, 235, Ptr, Ptr)]
        #[on(Arm, 269, Ptr, Ptr)]
        Utimes,
        #[on(X86, 190)]
        #[on(X86_64, 58)]
        #[on(Arm, 190)]
        Vfork,
        #[on(X86, 111)]
        #[on(X86_64, 153)]
        #[on(Arm, 111)]
        #[on(Aarch64, 58)]
        Vhangup,
        #[on(X86, 166, UWord, UWord)]
        Vm86,
        #[on(X86, 113, Ptr)]
        Vm86old,
        #[on(X86, 316, I(32), Ptr, UWord, U(32))]
        #[on(X86_64, 278, I(32), Ptr, UWord, U(32))]
        #[on(Arm, 343, I(32), Ptr, UWord, U(32))]
        #[on(Aarch64, 75, I(32), Ptr, UWord, U(32))]
        Vmsplice,
        #[on(X86, 273)]
        #[on(X86_64, 236)]
        #[on(Arm, 313)]
        Vserver,
        #[on(X86, 114, I(32), Ptr, I(32), Ptr)]
        #[on(X86_64, 61, I(32), Ptr, I(32), Ptr)]
        #[on(Arm, 114, I(32), Ptr, I(32), Ptr)]
        #[on(Aarch64, 260, I(32), Ptr, I(32), Ptr)]
        Wait4,
        #[on(X86, 284, I(32), I(32), Ptr, I(32), Ptr)]
        #[on(X86_64, 247, I(32), I(32), Ptr, I(32), Ptr)]
        #[on(Arm, 280, I(32), I(32), Ptr, I(32), Ptr)]
        #[on(Aarch64, 95, I(32), I(32), Ptr, I(32), Ptr)]
        Waitid,
        #[on(X86, 7, I(32), Ptr, I(32))]
        Waitpid,
        #[on(X86, 4, U(32), Ptr, UWord)]
        #[on(X86_64, 1, U(32), Ptr, UWord)]
        #[on(Arm, 4, U(32), Ptr, UWord)]
        #[on(Aarch64, 64, U(32), Ptr, UWord)]
        Write,
        #[on(X86, 146, UWord, Ptr, UWord)]
        #[on(X86_64, 20, UWord, Ptr, UWord)]
        #[on(Arm, 146, UWord, Ptr, UWord)]
        #[on(Aarch64, 66, UWord, Ptr, UWord)]
        Writev,
        // A special syscall to indicate it has been skipped.
        #[on(X86, -1)]
        #[on(X86_64, -1)]
        #[on(Arm, -1)]
        #[on(Aarch64, -1)]
        Skip,
    }
}

impl Syscall {
    /// `SYS_*` from `linux/net.h`: the call number under which x86 reaches this syscall through `socketcall`.
    pub open spec fn to_socketcall_arg(self) -> Option<u64> {
        match self {
            Syscall::Socket       => Some(1),
            Syscall::Bind         => Some(2),
            Syscall::Connect      => Some(3),
            Syscall::Listen       => Some(4),
            Syscall::Accept       => Some(5),
            Syscall::Getsockname  => Some(6),
            Syscall::Getpeername  => Some(7),
            Syscall::Socketpair   => Some(8),
            Syscall::Send         => Some(9),
            Syscall::Recv         => Some(10),
            Syscall::Sendto       => Some(11),
            Syscall::Recvfrom     => Some(12),
            Syscall::Shutdown     => Some(13),
            Syscall::Setsockopt   => Some(14),
            Syscall::Getsockopt   => Some(15),
            Syscall::Sendmsg      => Some(16),
            Syscall::Recvmsg      => Some(17),
            Syscall::Accept4      => Some(18),
            Syscall::Recvmmsg     => Some(19),
            Syscall::Sendmmsg     => Some(20),
            _ => None,
        }
    }
 
    /// `linux/ipc.h`: the call number under which x86 reaches this syscall through `ipc`.
    pub open spec fn to_ipc_arg(self) -> Option<u64> {
        match self {
            Syscall::Semop        => Some(1),
            Syscall::Semget       => Some(2),
            Syscall::Semctl       => Some(3),
            Syscall::Semtimedop   => Some(4),
            Syscall::Msgsnd       => Some(11),
            Syscall::Msgrcv       => Some(12),
            Syscall::Msgget       => Some(13),
            Syscall::Msgctl       => Some(14),
            Syscall::Shmat        => Some(21),
            Syscall::Shmdt        => Some(22),
            Syscall::Shmget       => Some(23),
            Syscall::Shmctl       => Some(24),
            _ => None,
        }
    }

    /// Whether the syscall symbol may match more than one
    /// concrete syscall numbers on one arch.
    pub open spec fn can_mux(self) -> bool {
        self.to_socketcall_arg() is Some || self.to_ipc_arg() is Some
    }
}

} // verus!
