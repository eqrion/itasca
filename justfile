# Rust -> Charon -> Aeneas -> Lean. See DEVELOPMENT.md.

default:
    @just --list

build:
    @cargo build

test:
    @make test

tools:
    @make tools

extract:
    @make extract

# Regenerate into a separate directory and reject stale committed models.
extract-check:
    @make extract-check

prove:
    @make prove

# Proof-health metrics. See lean/PROOF_ENGINEERING.md.
metrics:
    @cd lean && python3 scripts/metrics.py

# Static checks: layering, metric ratchet, links, and forbidden constructs.
lint:
    @cd lean && python3 scripts/metrics.py --violations
    @cd lean && python3 scripts/metrics.py --check metrics/baseline.json
    @cd lean && python3 scripts/check_links.py
    @cd lean && ! rg -n --glob '*.lean' --glob '!**/Generated/**' '\bsorry\b|\bnative_decide\b|^\s*axiom\b|^\s*admit\b' Itasca SpecExt

# Axioms and statement cone of the headline theorems. Builds first.
audit:
    @cd lean && lake build Itasca && lake env lean scripts/Audit.lean > metrics/audit.txt
    @git --no-pager diff --stat -- lean/metrics/audit.txt

check +modules:
    @cd lean && lake build {{ modules }}

# Build imports, then report elaboration/type-checking costs for one module.
profile module:
    @make profile MODULE={{ module }}

spec-check:
    @make spec-check

spec-update:
    @make spec-update

verify:
    @make verify

clean:
    @make clean

# Compatibility aliases for the port's recorded commands.
alias lean-extract := extract
alias lean-prove := prove

lean-spec:
    @make -C lean spec-generate
