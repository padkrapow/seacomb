# Changelog

All notable changes to this crate are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Added

- `Display` impls for various types in the policy AST.

### Changed

- A rule may now list architectures its policy does not enable, in which case
  it's not compiled for that architecture but still type-checked.
- New policy optimizer that merges similar rules and simplifies conditions.
  This reduces the number of cBPF instructions in `examples` by 19.4% in average
  on aarch64.

### Removed

- `CheckError::RuleArchNotEnabled`.

## [0.3.0] - 2026-09-29

### Added

- Rule conditions are now a typed expression language (`Cond`, `Expr`).
- New macros `policy!`, `rule!`, `cond!`, and `expr!` to construct policies.
- Expression are now type-checked against each syscall's C-level signature
  to avoid surprising bypasses.

### Changed

- API changes:
  - `Filter` is removed; use `Policy` and `Policy::add(Rule)` instead.
  - `ArgCmp` is replaced by `Cond`.
  - Install options move to `InstallFlags` and `Policy::install_with_flags`.
  - Validation errors move to the new `CheckError`.
  - cBPF types move to the `cbpf` module.

## [0.2.0] - 2026-09-24

### Changed

- API improvements:
  - Add `Filter::add_rule_exact`, which matches only the syscall's own number
    and not its x86 `socketcall`/`ipc` multiplexed form. `Rule` gains a
    `no_mux` field for this.
  - Error types now implement `std::error::Error` via `thiserror` and are
    `#[non_exhaustive]`. `Error::InvalidErrno` carries the rejected value.
  - New errors: `Error::InvalidMuxConditions` and `Error::NoArch` (returned by
    `Filter::install` when no architecture is enabled).

### Security

- Fix some potential security issues:
  - On x86, a rule for an `ipc` subcall now matches on the low 16 bits of the
    call number, as the kernel does. Before, setting the high bits of the
    call number bypassed the rule.
  - On x86, a rule with argument conditions for a `socketcall`/`ipc` subcall
    (e.g. `bind`) silently did not apply to the multiplexed call. Such rules are
    now rejected with `Error::InvalidMuxConditions`; use
    `Filter::add_rule_exact` to match the direct syscall only.

### Fixed

- On x86_64, syscall number -1 (used by tracers to skip a syscall) is no longer
  treated as a bad-arch x32 syscall.

## [0.1.0] - 2026-09-23 [YANKED]

- Initial release of seacomb.

[Unreleased]: https://github.com/thai-terrace/seacomb/compare/v0.3.0...HEAD
[0.3.0]: https://github.com/thai-terrace/seacomb/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/thai-terrace/seacomb/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/thai-terrace/seacomb/releases/tag/v0.1.0
