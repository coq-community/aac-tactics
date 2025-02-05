# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [9.0.0] - 2025-02-05

### Changed

- Clarify tactics and their options in the tutorial, in particular `in_right` for `aac_rewrite`

### Fixed

- compatibility with for Rocq 9.0

## [8.20.0] - 2024-06-27

### Added

- Tests for `try aac_rewrite` and `try aac_normalise` that failed on 8.19

## [8.19.1] - 2024-06-01

### Added

- `aac_normalise in H` tactic.
- `gcd` and `lcm` instances for `Nat`, `N`, and `Z`.

### Fixed

- Make the order of sums produced by `aac_normalise` tactic consistent across calls.

[Unreleased]: https://github.com/coq-community/aac-tactics/compare/v9.0.0...master
[9.0.0]: https://github.com/coq-community/aac-tactics/compare/v9.0.0
[8.20.0]: https://github.com/coq-community/aac-tactics/compare/v8.20.0
[8.19.1]: https://github.com/coq-community/aac-tactics/releases/tag/v8.19.1
