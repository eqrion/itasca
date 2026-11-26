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
alias profile := lean::profile
alias prove := lean::prove
alias spec-check := lean::spec-check
alias spec-update := lean::spec-update
alias tools := lean::tools

build:
    @cargo build

test:
    @cargo test
    @cargo test --no-default-features

# Compare generated sources before building and auditing the proofs.
verify: test lean::extract-check lean::spec-compare lean::audit
