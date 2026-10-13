# Active verification pipeline: Rust -> Charon -> Aeneas -> Lean.
.DEFAULT_GOAL := prove

.PHONY: all build test tools extract extract-check prove check profile trust spec-check \
        spec-update regressions verify clean

all: prove

build:
	cargo build

test:
	cargo test
	cargo test --no-default-features

tools extract extract-check prove trust spec-check spec-update regressions clean:
	$(MAKE) -C lean $@

# Example: make check MODULE=Itasca.Module.Validation
check:
	@test -n "$(MODULE)" || { echo "Set MODULE=Itasca.ModuleName"; exit 1; }
	cd lean && lake build $(MODULE)

profile:
	@test -n "$(MODULE)" || { echo "Set MODULE=Itasca.ModuleName"; exit 1; }
	cd lean && lake lean $(subst .,/,$(MODULE)).lean -- --profile

# Keep toolchain regeneration and Lake builds sequential, including under -j.
verify:
	$(MAKE) test
	$(MAKE) extract-check
	# The final integrated build compiles the specification and SpecChecks.
	$(MAKE) -C lean spec-compare
	$(MAKE) regressions
	$(MAKE) prove
