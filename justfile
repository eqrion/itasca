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

check +modules:
    @cd lean && lake build {{ modules }}

# Build imports, then report elaboration/type-checking costs for one module.
profile module:
    @make profile MODULE={{ module }}

trust:
    @make trust

# Point Itasca.Audit at the current sink modules after adding or moving files.
audit-imports:
    @make -C lean audit-imports

spec-check:
    @make spec-check

spec-update:
    @make spec-update

regressions:
    @make regressions

verify:
    @make verify

clean:
    @make clean

# Compatibility aliases for the port's recorded commands.
alias lean-extract := extract
alias lean-prove := prove

lean-spec:
    @make -C lean spec-generate
