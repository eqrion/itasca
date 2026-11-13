# Rust extraction, specification generation and Lean verification.
ROOT := $(abspath ..)
include toolchain.mk
SPECTEC_DIR := $(ROOT)/vendor/spectec/spectec
SPECTEC := $(SPECTEC_DIR)/_build/default/src/exe-spectec/main.exe
SPECTEC_PATCH := $(ROOT)/patches/spectec-wasm2-global-mutability.patch
SPECTEC_BUILTINS_PATCH := $(ROOT)/patches/spectec-wasm2-builtins.patch
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
# Current Charon reads Cargo metadata rather than the retired Charon.toml.
# Keep the verified extraction configuration explicit here.
CHARON_FLAGS := --preset=aeneas --sysroot=default --rustc-arg=--cfg=charon \
	--exclude='{impl core::clone::Clone for _}' \
	--exclude='{impl core::marker::Copy for _}' \
	--include='core::marker::{impl core::marker::Copy for u8}' \
	--include='core::clone::impls::{impl core::clone::Clone for u8}'

.PHONY: tools patch-spectec check-tools extract extract-check llbc \
 prove clean checkpoint spec-build spec-generate spec-update \
 spec-compare spec-check

# Source patches are repeatable and fail if the checkout has incompatible edits.
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

tools:
	sh install-tools.sh "$(TOOLS_DIR)" "$(AENEAS_REV)" "$(RUST_TOOLCHAIN)" "$(OPAM_SWITCH)"

check-tools:
	@test -x "$(AENEAS)" -a -x "$(CHARON)" -a -x "$(TOOLS_DIR)/bin/charon-driver" || { echo "Run just tools to install the pinned extraction tools."; exit 1; }

# Keep extraction outputs separate from ordinary Rust tests and release builds.
llbc: check-tools
	mkdir -p .build
	cd $(ROOT) && RUSTUP_TOOLCHAIN=$(RUST_TOOLCHAIN) CARGO_TARGET_DIR=$(CURDIR)/.build/cargo $(CHARON) cargo $(CHARON_FLAGS) --dest-file=$(CURDIR)/.build/itasca.llbc

extract: llbc
	$(AENEAS) -backend lean .build/itasca.llbc -dest . -subdir /Itasca/Generated -split-files -namespace Itasca -no-progress-bar
	python3 scripts/strip_source_lines.py Itasca/Generated/Types.lean Itasca/Generated/Funs.lean

# Do not refresh checked-in files while checking their provenance.
extract-check: llbc
	mkdir -p .build/extract-check
	$(AENEAS) -backend lean .build/itasca.llbc -dest .build/extract-check -subdir /Itasca/Generated -split-files -namespace Itasca -no-progress-bar
	python3 scripts/strip_source_lines.py .build/extract-check/Itasca/Generated/Types.lean .build/extract-check/Itasca/Generated/Funs.lean
	cmp .build/extract-check/Itasca/Generated/Types.lean Itasca/Generated/Types.lean
	cmp .build/extract-check/Itasca/Generated/Funs.lean Itasca/Generated/Funs.lean

prove:
	lake build Itasca SpecExt

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
	mkdir -p .build/spec
	cd $(SPECTEC_DIR) && $(SPECTEC) ../specification/wasm-2.0/*.spectec --lean --single-pattern-match --wf-state all -o $(CURDIR)/.build/spec/wasm2.0.lean
	patch -f -F 0 -p1 -d .build/spec < $(SPECTEC_BUILTINS_PATCH)

spec-update: spec-generate
	mkdir -p SpecTec
	cp .build/spec/wasm2.0.lean SpecTec/

spec-compare: spec-generate
	cmp .build/spec/wasm2.0.lean SpecTec/wasm2.0.lean

spec-check: spec-compare
	lake build SpecTecGenerated Itasca.Spec.Checks
