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
filter.add(rule!(errno(1) write(fd, buf, count) when fd == 2u32)).unwrap();

// Kill the process on execve.
filter.add(rule!(kill process execve(pathname, argv, envp))).unwrap();

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

## Trusted computing base and how AI agents are involved

Formal verification helps reducing the amount of code we need to *trust*,
by machine-checking the executable code against simpler formal/mathemtical
specifications and properties.

Using this method, this repo implicitly has two kinds of code/proofs:
(a) trusted specifications that need to be carefully edited and manually audited,
and (b) executable code and proofs that do not need to be trusted.

Part (a) is mostly contained in `src/spec/`, including the syntax and semantics of
`seacomb`'s policy DSL, cBPF, and type signatures of all supported syscalls.
These specs were written with assistance of AI agents, but heavily audited and understood manually.

Part (b) notably includes the compiler implementation and its correctness proofs in
`src/compiler.rs` and `src/compiler/`.
They are mostly generated using Claude Code and Codex,
but their *correctness* against the specs in `src/spec/` is automatically verified by
[Verus](https://github.com/verus-lang/verus).

There are some other components that are in a "gray area," which are verified for simpler
properties like panic-freedom and termination, but they are not verified to be functionally correct
or lacking formal specs.
The assembler in `src/asm.rs` is an example, which is used for converting an AST of cBPF program
to actual binary formats used by the kernel.
The actual installaion of the policies (`Filter::install` and `RawProgram::install_with_flags`)
is also not verified and marked `unsafe` since it requires low-level syscalls.

## Related work

- [Jitk: A Trustworthy In-Kernel Interpreter Infrastructure](https://dl.acm.org/doi/10.5555/2685048.2685052)
- [libseccomp](https://github.com/seccomp/libseccomp)
  (Rust binding: [libseccomp-rs](https://github.com/libseccomp-rs/libseccomp-rs))
- [seccompiler](https://github.com/rust-vmm/seccompiler)
