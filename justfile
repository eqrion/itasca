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
    @make lint

# Check handwritten warning counts using the completed build's cached traces.
warnings:
    @cd lean && python3 scripts/lean_warnings.py --check

# Check the public surface and all artifacts; --update refreshes them explicitly.
audit *args:
    @make audit AUDIT_ARGS='{{args}}'

tooling-test:
    @make tooling-test

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


lean-spec:
    @make -C lean spec-generate
