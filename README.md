# seacomb: formally verified seccomp compiler

[![crates.io](https://img.shields.io/crates/v/seacomb.svg)](https://crates.io/crates/seacomb)
[![docs.rs](https://img.shields.io/docsrs/seacomb)](https://docs.rs/seacomb)

`seacomb` is a Rust library for compiling and enforcing
[seccomp](https://man7.org/linux/man-pages/man2/seccomp.2.html) policies,
which is a Linux kernel feature for filtering/intercepting syscalls and sandboxing.
For example, [Chrome](https://chromium.googlesource.com/chromium/src/+/main/sandbox/linux/README.md)
and [Firefox](https://wiki.mozilla.org/Security/Sandbox/Seccomp)
use seccomp to sandbox the processes that render web pages,
and [Docker](https://docs.docker.com/engine/security/seccomp/)
and [systemd](https://www.freedesktop.org/software/systemd/man/latest/systemd.exec.html#SystemCallFilter=)
use it to restrict containers and services.

By declaring rules in a similar style to [libseccomp](https://github.com/seccomp/libseccomp),
`seacomb` compiles and registers these rules using a *formally verified* compiler to cBPF.

```rust
use seacomb::*;
use std::io::Write;

// Allow any syscall when no rule matches.
let mut filter = Filter::new_native(Action::Allow).unwrap();

// Make write to stderr (fd 2) fail with EPERM.
let stderr = Expr::Var(0).eq(Expr::Lit(2, PrimType::U(32)));
filter.add_rule(Action::Errno(1), Syscall::Write, stderr).unwrap();

// Kill the process on execve.
filter.add_rule(Action::KillProcess, Syscall::Execve, Cond::True).unwrap();

#[cfg(target_os = "linux")]
{
    filter.install().unwrap();

    assert!(std::io::stdout().write_all(b"Hello from stdout!\n").is_ok());
    let err = std::io::stderr().write_all(b"Hello from stderr!\n").unwrap_err();
    assert_eq!(err.raw_os_error(), Some(1));
}
```

Supported architectures: x86, x86-64, 32-bit ARM (little-endian), and AArch64.

## What has been formally verified

`seacomb` is developed using [Verus](https://github.com/verus-lang/verus),
an automated program verifier for Rust.

Formally verified properties:
- **Compiler correctness:** `seacomb`'s policy compiler always produces cBPF filters equivalent to the source policy, relative to the formal semantics of policies and cBPF in `src/spec`.
  This rules out miscompilations like these in libseccomp:
  - [CVE-2019-9893](https://github.com/seccomp/libseccomp/issues/139):
    64-bit `<`, `<=`, `>`, `>=` argument comparisons were generated incorrectly,
    so filters could be bypassed.
  - [#148](https://github.com/seccomp/libseccomp/issues/148):
    the optimizer merged code blocks that were not actually duplicates,
    which broke Tor's sandbox.
  - [GHSA-4q85-33p6-j5g6](https://github.com/seccomp/libseccomp/security/advisories/GHSA-4q85-33p6-j5g6):
    merging overlapping 64-bit comparison rules let denied syscalls through.
- **Determinism:** A policy picks exactly one action for each syscall.
- **Chaining:** Installing multiple policies is equivalent to evaluating them
  in order, verified against the kernel's precedence and tie-breaking rules.

To verify the proofs, [install Verus](https://github.com/verus-lang/verus/blob/main/INSTALL.md),
and run:
```sh
cargo verus verify
```
Without verification, this crate is also completely compatible with `cargo`.

## Testing

QEMU is a prerequisite for testing (install with, e.g., `brew install qemu`).

To run all tests on all supported architectures, or on one:
```sh
python3 tests/run.py
python3 tests/run.py aarch64
```

## Related work

- [Jitk: A Trustworthy In-Kernel Interpreter Infrastructure](https://dl.acm.org/doi/10.5555/2685048.2685052)
- [libseccomp](https://github.com/seccomp/libseccomp)
  (Rust binding: [libseccomp-rs](https://github.com/libseccomp-rs/libseccomp-rs))
- [seccompiler](https://github.com/rust-vmm/seccompiler)
