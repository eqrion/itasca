# Active verification pipeline: Rust -> Charon -> Aeneas -> Lean.
.DEFAULT_GOAL := prove

.PHONY: all build test tools extract extract-check prove check profile spec-check \
        spec-update verify clean lint warnings audit tooling-test

AUDIT_ARGS ?=

all: prove

build:
	cargo build

test:
	cargo test
	cargo test --no-default-features

tools extract extract-check prove spec-check spec-update clean:
	$(MAKE) -C lean $@

# Example: make check MODULE=Itasca.Results.Validate
check:
	@test -n "$(MODULE)" || { echo "Set MODULE=Itasca.ModuleName"; exit 1; }
	cd lean && lake build $(MODULE)

profile:
	@test -n "$(MODULE)" || { echo "Set MODULE=Itasca.ModuleName"; exit 1; }
	cd lean && lake lean $(subst .,/,$(MODULE)).lean -- --profile

# Source-only architecture, proof-health ratchets, links and forbidden constructs.
lint:
	cd lean && python3 scripts/architecture.py
	cd lean && python3 scripts/metrics.py --check metrics/baseline.json
	cd lean && python3 scripts/check_links.py
	cd lean && python3 scripts/check_forbidden.py
	cd lean && python3 scripts/check_namespaces.py

tooling-test:
	cd lean && python3 -m unittest discover -s scripts -p 'test_*.py'

# Requires the current integrated build; does not elaborate modules again.
warnings:
	cd lean && python3 scripts/lean_warnings.py --check

# Checks by default; use AUDIT_ARGS=--update to refresh artifacts explicitly.
audit:
	cd lean && python3 scripts/run_audit.py $(AUDIT_ARGS)

# Keep toolchain regeneration and Lake builds sequential, including under -j.
verify:
	$(MAKE) test
	$(MAKE) tooling-test
	$(MAKE) lint
	$(MAKE) extract-check
	# The final integrated build compiles the specification and declared-reference checks.
	$(MAKE) -C lean spec-compare
	$(MAKE) prove
	$(MAKE) warnings
	$(MAKE) audit AUDIT_ARGS=--no-build
