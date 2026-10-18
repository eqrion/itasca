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
AENEAS_REUSE_PATCH := $(ROOT)/patches/aeneas-reuse-definitions.patch
SPECTEC_PATCH := $(ROOT)/patches/spectec-wasm2-global-mutability.patch
SPECTEC_MODULE_PATCH := $(ROOT)/patches/spectec-wasm2-module.patch
SPECTEC_HOSTFUNC_PATCH := $(ROOT)/patches/spectec-wasm2-hostfunc.patch
SPECTEC_INTEGER_PATCH := $(ROOT)/patches/spectec-wasm2-integer-domains.patch
SPECTEC_MEMORY_PATCH := $(ROOT)/patches/spectec-wasm2-memory-boundary.patch
TEST_RUNNER := $(AENEAS_DIR)/tests/test_runner/_build/default/run_test.exe
# Current Charon reads Cargo metadata rather than the retired Charon.toml.
# Keep the verified extraction configuration explicit here.
CHARON_FLAGS := --preset=aeneas --sysroot=default --rustc-arg=--cfg=charon \
	--exclude='{impl core::clone::Clone for _}' \
	--exclude='{impl core::marker::Copy for _}'

.PHONY: tools patch-aeneas patch-spectec aeneas-build extract extract-check llbc \
 extract-primary extract-check-primary llbc-exec extract-exec extract-check-exec \
 prove prove-exec trust script-tests audit-coverage audit-imports clean checkpoint spec-build spec-generate spec-update \
 spec-compare spec-check regressions

# Source patches are repeatable and fail if the checkout has incompatible edits.
patch-aeneas:
	cd $(AENEAS_DIR) && { git apply --reverse --check $(AENEAS_PATCH) 2>/dev/null || git apply $(AENEAS_PATCH); }
	cd $(AENEAS_DIR) && { git apply --reverse --check $(AENEAS_REUSE_PATCH) 2>/dev/null || git apply $(AENEAS_REUSE_PATCH); }

patch-spectec:
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_PATCH) 2>/dev/null || git apply $(SPECTEC_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_MODULE_PATCH) 2>/dev/null || git apply $(SPECTEC_MODULE_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_HOSTFUNC_PATCH) 2>/dev/null || git apply $(SPECTEC_HOSTFUNC_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_INTEGER_PATCH) 2>/dev/null || git apply $(SPECTEC_INTEGER_PATCH); }
	cd $(ROOT)/vendor/spectec && { git apply --reverse --check $(SPECTEC_MEMORY_PATCH) 2>/dev/null || git apply $(SPECTEC_MEMORY_PATCH); }

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

extract-primary: aeneas-build llbc
	$(AENEAS) -backend lean .build/itasca.llbc -dest . -subdir /Itasca/Generated -split-files -namespace Itasca -no-progress-bar

# Do not refresh checked-in files while checking their provenance.
extract-check-primary: aeneas-build llbc
	mkdir -p .build/extract-check
	$(AENEAS) -backend lean .build/itasca.llbc -dest .build/extract-check -subdir /Itasca/Generated -split-files -namespace Itasca -no-progress-bar
	cmp .build/extract-check/Itasca/Generated/Types.lean Itasca/Generated/Types.lean
	cmp .build/extract-check/Itasca/Generated/Funs.lean Itasca/Generated/Funs.lean
	python3 scripts/check_externals.py .build/extract-check/Itasca/Generated/FunsExternal_Template.lean

# The runtime map is derived from the canonical validator model. Keep the two
# passes sequential, including under make -j, and retain primary-only targets
# for bootstrap and byte-for-byte validator regression checks.
llbc-exec: llbc
	python3 scripts/extract_execution.py llbc

extract-exec: extract-primary
	python3 scripts/extract_execution.py llbc
	python3 scripts/extract_execution.py translate

extract-check-exec: extract-check-primary
	python3 scripts/extract_execution.py llbc
	python3 scripts/extract_execution.py check

extract: extract-exec

extract-check: extract-check-exec

script-tests:
	python3 -m unittest discover -s scripts -p 'test_*.py'

audit-coverage: script-tests
	python3 scripts/check_audit.py

# Point each library audit at its current sink modules.
audit-imports:
	python3 scripts/check_audit.py --write

prove: audit-coverage
	lake build

prove-exec: audit-coverage
	lake build SpecExt.Audit Exec.Audit

trust: prove
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
	python3 scripts/probe_reuse.py
