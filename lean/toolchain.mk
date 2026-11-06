# Keep AENEAS_REV in sync with lakefile.lean and lake-manifest.json.
AENEAS_REV := 557eff83ecef5083b98a52a94ca7fae63d6c1dab
RUST_TOOLCHAIN := nightly-2026-09-17
OPAM_SWITCH ?= itasca-lean
TOOLS_CACHE ?= $(if $(XDG_CACHE_HOME),$(XDG_CACHE_HOME),$(HOME)/.cache)/itasca
TOOLS_DIR := $(TOOLS_CACHE)/aeneas-$(AENEAS_REV)
AENEAS := $(TOOLS_DIR)/bin/aeneas
CHARON := $(TOOLS_DIR)/bin/charon
