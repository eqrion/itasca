# Active verification pipeline: Rust -> Charon -> Aeneas -> Lean.
.DEFAULT_GOAL := prove

.PHONY: all build test tools extract extract-check prove check trust spec-check \
        spec-update regressions verify clean

all: prove

build:
	cargo build

test:
	cargo test
	cargo test --no-default-features

tools extract extract-check prove trust spec-check spec-update regressions clean:
	$(MAKE) -C lean $@

# Example: make check MODULE=Itasca.ModuleValidation
check:
	@test -n "$(MODULE)" || { echo "Set MODULE=Itasca.ModuleName"; exit 1; }
	cd lean && lake build $(MODULE)

# Keep toolchain regeneration and Lake builds sequential, including under -j.
verify:
	$(MAKE) test
	$(MAKE) extract-check
	$(MAKE) spec-check
	$(MAKE) regressions
	$(MAKE) prove
