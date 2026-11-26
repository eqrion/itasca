# Rust -> Charon -> Aeneas -> Lean. See DEVELOPMENT.md.

mod lean 'lean/justfile'

default:
    @just --list

alias all := lean::prove
alias audit := lean::audit
alias check := lean::check
alias clean := lean::clean
alias extract := lean::extract
alias extract-check := lean::extract-check
alias lean-spec := lean::spec-generate
alias lint := lean::lint
alias metrics := lean::metrics
alias profile := lean::profile
alias prove := lean::prove
alias spec-check := lean::spec-check
alias spec-update := lean::spec-update
alias tooling-test := lean::tooling-test
alias tools := lean::tools
alias warnings := lean::warnings

build:
    @cargo build

test:
    @cargo test
    @cargo test --no-default-features

# Compare generated sources before the integrated build and reuse it for audit.
verify: test lean::tooling-test lean::lint lean::extract-check lean::spec-compare lean::prove lean::warnings (lean::audit "--no-build")
