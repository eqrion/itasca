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

# Runtime extraction first refreshes its canonical validator dependencies.
extract-exec:
    @make extract-exec

extract-check-exec:
    @make extract-check-exec

# Keep the validator pass independently available for bootstrap and regressions.
extract-primary:
    @make extract-primary

extract-check-primary:
    @make extract-check-primary

llbc-exec:
    @make llbc-exec

prove:
    @make prove

# Check execution proofs and handwritten specification extensions.
prove-exec:
    @make prove-exec

check +modules:
    @cd lean && lake build {{ modules }}

# Build imports, then report elaboration/type-checking costs for one module.
profile module:
    @make profile MODULE={{ module }}

trust:
    @make trust

# Refresh each library audit after adding or moving proof files.
audit-imports:
    @make audit-imports

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
