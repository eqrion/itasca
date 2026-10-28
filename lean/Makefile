# Rust extraction, specification generation and Lean verification.
ROOT := $(abspath ..)
AENEAS_DIR := $(ROOT)/vendor/aeneas-lean
SPECTEC_DIR := $(ROOT)/vendor/spectec/spectec
OPAM_SWITCH ?= itasca-lean
CHARON := $(AENEAS_DIR)/charon/charon/target/release/charon
AENEAS := $(AENEAS_DIR)/src/_build/default/main.exe
SPECTEC := $(SPECTEC_DIR)/_build/default/src/exe-spectec/main.exe
RUST_TOOLCHAIN := nightly-2026-09-17
AENEAS_PATCH := $(ROOT)/patches/aeneas-lean-extraction.patch
SPECTEC_PATCH := $(ROOT)/patches/spectec-wasm2-global-mutability.patch
SPECTEC_MODULE_PATCH := $(ROOT)/patches/spectec-wasm2-module.patch
SPECTEC_HOSTFUNC_PATCH := $(ROOT)/patches/spectec-wasm2-hostfunc.patch
SPECTEC_INTEGER_PATCH := $(ROOT)/patches/spectec-wasm2-integer-domains.patch
SPECTEC_HOST_TYPING_PATCH := $(ROOT)/patches/spectec-wasm2-host-typing.patch
SPECTEC_LANE_PATCH := $(ROOT)/patches/spectec-wasm2-lane-store.patch
SPECTEC_LOAD_VALUE_BOUNDS_PATCH := $(ROOT)/patches/spectec-wasm2-load-value-bounds.patch
SPECTEC_WRITE_BOUNDS_PATCH := $(ROOT)/patches/spectec-wasm2-memory-write-bounds.patch
SPECTEC_TABLE_WRITE_BOUNDS_PATCH := $(ROOT)/patches/spectec-wasm2-table-write-bounds.patch
SPECTEC_EXPORT_MEMBERSHIP_PATCH := $(ROOT)/patches/spectec-wasm2-export-membership.patch
SPECTEC_MEMORY_PATCH := $(ROOT)/patches/spectec-wasm2-memory-boundary.patch
TEST_RUNNER := $(AENEAS_DIR)/tests/test_runner/_build/default/run_test.exe
# Current Charon reads Cargo metadata rather than the retired Charon.toml.
# Keep the verified extraction configuration explicit here.
CHARON_FLAGS := --preset=aeneas --sysroot=default --rustc-arg=--cfg=charon \
	--exclude='{impl core::clone::Clone for _}' \
	--exclude='{impl core::marker::Copy for _}' \
	--include='core::marker::{impl core::marker::Copy for u8}' \
	--include='core::clone::impls::{impl core::clone::Clone for u8}'

.PHONY: tools patch-aeneas patch-spectec aeneas-build extract extract-check llbc \
 prove trust script-tests audit-coverage audit-imports clean checkpoint spec-build spec-generate spec-update \
 spec-compare spec-check regressions

# Source patches are repeatable and fail if the checkout has incompatible edits.
patch-aeneas:
	cd $(AENEAS_DIR) && { git apply --reverse --check $(AENEAS_PATCH) 2>/dev/null || git apply $(AENEAS_PATCH); }

patch-spectec:
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_PATCH) 2>/dev/null || git apply $(SPECTEC_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_MODULE_PATCH) 2>/dev/null || git apply $(SPECTEC_MODULE_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_HOSTFUNC_PATCH) 2>/dev/null || git apply $(SPECTEC_HOSTFUNC_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_INTEGER_PATCH) 2>/dev/null || git apply $(SPECTEC_INTEGER_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_MEMORY_PATCH) 2>/dev/null || git apply $(SPECTEC_MEMORY_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_LANE_PATCH) 2>/dev/null || git apply $(SPECTEC_LANE_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_HOST_TYPING_PATCH) 2>/dev/null || git apply $(SPECTEC_HOST_TYPING_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_WRITE_BOUNDS_PATCH) 2>/dev/null || git apply $(SPECTEC_WRITE_BOUNDS_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_EXPORT_MEMBERSHIP_PATCH) 2>/dev/null || git apply $(SPECTEC_EXPORT_MEMBERSHIP_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_TABLE_WRITE_BOUNDS_PATCH) 2>/dev/null || git apply $(SPECTEC_TABLE_WRITE_BOUNDS_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_LOAD_VALUE_BOUNDS_PATCH) 2>/dev/null || git apply $(SPECTEC_LOAD_VALUE_BOUNDS_PATCH); }

tools: patch-aeneas
	cd $(AENEAS_DIR)/charon/charon && RUSTUP_TOOLCHAIN=$(RUST_TOOLCHAIN) cargo build --release --locked --bin charon --bin charon-driver
	$(MAKE) -C $(AENEAS_DIR)/charon charon-ml/src/CharonVersion.ml
	cd $(AENEAS_DIR)/src && opam exec --switch=$(OPAM_SWITCH) -- dune build main.exe

aeneas-build: patch-aeneas
	cd $(AENEAS_DIR)/src && opam exec --switch=$(OPAM_SWITCH) -- dune build main.exe

# Keep extraction outputs separate from ordinary Rust tests and release builds.
llbc:
	mkdir -p .build
	cd $(ROOT) && RUSTUP_TOOLCHAIN=$(RUST_TOOLCHAIN) CARGO_TARGET_DIR=$(CURDIR)/.build/cargo $(CHARON) cargo $(CHARON_FLAGS) --dest-file=$(CURDIR)/.build/itasca.llbc

extract: aeneas-build llbc
	$(AENEAS) -backend lean .build/itasca.llbc -dest . -subdir /Itasca/Generated -split-files -namespace Itasca -no-progress-bar

# Do not refresh checked-in files while checking their provenance.
extract-check: aeneas-build llbc
	mkdir -p .build/extract-check
	$(AENEAS) -backend lean .build/itasca.llbc -dest .build/extract-check -subdir /Itasca/Generated -split-files -namespace Itasca -no-progress-bar
	cmp .build/extract-check/Itasca/Generated/Types.lean Itasca/Generated/Types.lean
	cmp .build/extract-check/Itasca/Generated/Funs.lean Itasca/Generated/Funs.lean
	python3 scripts/check_externals.py .build/extract-check/Itasca/Generated/FunsExternal_Template.lean

script-tests:
	python3 -m unittest discover -s scripts -p 'test_*.py'

audit-coverage: script-tests
	python3 scripts/check_audit.py

# Point each library audit at its current sink modules.
audit-imports:
	python3 scripts/check_audit.py --write

prove: audit-coverage
	lake build Itasca SpecExt.Audit
	mkdir -p .build
	lake env lean --run scripts/reachability.lean --check .build/dead.txt

# Headline theorems first, then every validator declaration.
trust: prove
	lake env lean --run scripts/trust.lean
	ITASCA_AUDIT_VERBOSE=1 lake env lean Itasca/Audit.lean

# Preserve dependency caches; remove only this project's compiled artifacts.
clean:
	rm -rf .lake/build

# Check the spec and concrete external models independently of the Rust model.
checkpoint:
	lake build Itasca.Spec.Checks Itasca.Generated.FunsExternal

spec-build: patch-spectec
	$(MAKE) -C $(SPECTEC_DIR) src/backend-interpreter/reference-interpreter
	cd $(SPECTEC_DIR) && opam exec --switch=$(OPAM_SWITCH) -- dune build src/exe-spectec/main.exe

# The local generated source is committed alongside the extracted Rust model.
# Never overwrite the upstream checkpoint or edit generated Lean by hand.
spec-generate: spec-build
	mkdir -p .build
	cd $(SPECTEC_DIR) && $(SPECTEC) ../specification/wasm-2.0/*.spectec --lean --single-pattern-match --wf-state all -o $(CURDIR)/.build/wasm2.0.raw.lean
	python3 scripts/spec_split.py .build/wasm2.0.raw.lean .build/spec

spec-update: spec-generate
	mkdir -p SpecTec
	cp .build/spec/Wasm2Prefix.lean .build/spec/wasm2.0.lean .build/spec/Wasm2Builtins.lean SpecTec/

spec-compare: spec-generate
	cmp .build/spec/Wasm2Prefix.lean SpecTec/Wasm2Prefix.lean
	cmp .build/spec/wasm2.0.lean SpecTec/wasm2.0.lean
	cmp .build/spec/Wasm2Builtins.lean SpecTec/Wasm2Builtins.lean

spec-check: spec-compare
	python3 -m unittest discover -s scripts -p test_spec_split.py
	lake build SpecTecGenerated Itasca.Spec.Checks

# Use upstream's test runner and compile its regenerated outputs in our Lake env.
regressions: aeneas-build
	lake build Aeneas
	cd $(AENEAS_DIR)/tests/test_runner && opam exec --switch=$(OPAM_SWITCH) -- dune build run_test.exe
	cd $(AENEAS_DIR) && RUSTUP_TOOLCHAIN=$(RUST_TOOLCHAIN) gmake IN_CI=1 AENEAS_EXE=$(AENEAS) CHARON_EXE=$(CHARON) TEST_RUNNER_EXE=$(TEST_RUNNER) test-namespace-shadow.rs test-deep-else-if.rs
	lake env lean $(AENEAS_DIR)/tests/lean/NamespaceShadow.lean
	lake env lean $(AENEAS_DIR)/tests/lean/DeepElseIf.lean
