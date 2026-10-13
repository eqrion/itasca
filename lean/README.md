# Lean verification

Lean checks the extracted Rust validator against SpecTec-generated Wasm 2.0
typing rules, an independent binary grammar, and explicit Wasm 1.0 and Wasm 2.0
profiles. The [project README](../README.md#formal-verification) states the
public guarantees and trust boundary, and [DEVELOPMENT.md](../DEVELOPMENT.md)
the change workflow. This guide covers setup, proof contracts, and layout. If
you are new to Lean, start with [A guide to the itasca proofs](PROOF_GUIDE.md).

## Setup

| Component | Pin |
| --- | --- |
| Aeneas | `557eff83ecef5083b98a52a94ca7fae63d6c1dab` |
| Charon | `c8f15d7d658c86a95658f71ad99cddd4be002e04`, from Aeneas's `charon-pin` |
| Rust for Charon | `nightly-2026-09-17` |
| Lean and Mathlib | `v4.31.0` |
| SpecTec | `edc84f7ec81f927f3fdb952a82ecd38fed8e4f29` |
| OCaml and Dune | `5.2.0` and `3.23.1`, in the `itasca-lean` opam switch |

From the repository root:

```sh
git submodule update --init vendor/aeneas-lean vendor/spectec tests/third_party/wasm-spec

opam switch create itasca-lean ocaml-base-compiler.5.2.0 --no-switch -y
opam install --switch=itasca-lean -y dune.3.23.1 dune-build-info.3.23.1 \
  ocamlformat.0.27.0 calendar core_unix \
  domainslib easy_logging menhir ocamlgraph ppx_deriving ppx_deriving_yojson \
  progress unionFind visitors yojson zarith pprint

git clone https://github.com/AeneasVerif/charon.git vendor/aeneas-lean/charon
git -C vendor/aeneas-lean/charon checkout "$(tail -n 1 vendor/aeneas-lean/charon-pin)"
rustup toolchain install nightly-2026-09-17 --profile minimal \
  --component rustc-dev,rust-src,llvm-tools
elan toolchain install leanprover/lean4:v4.31.0
make -C lean tools
cd lean
lake exe cache get
```

Use the committed `lake-manifest.json`; builds do not need `lake update`.
`OPAM_SWITCH` selects another compatible switch. Dune stays at 3.23.1 because
3.24 rejects SpecTec's nested legacy Coq project. SpecTec's own Lake project
selects Lean 4.32, but its generated output compiles here on 4.31.

## Commands

```sh
just extract          # Rust -> LLBC -> committed Lean program model
just extract-check    # Regenerate separately and reject stale models
just check Itasca.Module.Validation  # Build specific modules
just profile Itasca.Wasm2.Step.ScalarContext  # Profile one file's elaboration
just prove            # Check audit coverage and build all proofs
just audit-imports    # Regenerate Itasca.Audit's imports
just trust            # Rerun the detailed axiom report
just spec-update      # Copy a regenerated specification into the source tree
just spec-check       # Regenerate, compare, and compile the specification
just regressions      # Extract and compile Aeneas regression cases
just verify           # Rust tests and all verification checks
```

Preserve the `.lake/` and `.build/` caches.

## Generated sources

[Generated/Types.lean](Itasca/Generated/Types.lean) and
[Funs.lean](Itasca/Generated/Funs.lean) come from `just extract`; never edit them
by hand. [FunsExternal.lean](Itasca/Generated/FunsExternal.lean) is the
handwritten model of `Vec.pop` and `Vec.is_empty`. The generated external
template is ignored and must not be imported.

[SpecTec/wasm2.0.lean](SpecTec/wasm2.0.lean) is generated from the pinned SpecTec
sources and the patches below, and checked byte for byte by `just spec-check`.
The `SpecTecSupport` library compiles upstream's handwritten
`ExtendedDeriveDecEq.lean`. Neither relies on upstream compiled artifacts.

## Proof contracts

`profile_*` theorems quantify over both `ValidationProfile` values; `wasm_*`
corollaries specialize to Wasm 1.0.

| Layer | Contracts |
| --- | --- |
| Whole module | [Module/Validation](Itasca/Module/Validation.lean): `module.validate_module.profile_total`, `profile_sound`, `profile_spec`. [Module/Completeness](Itasca/Module/Completeness.lean): `profile_complete`, `profile_complete_with_metadata`. |
| Streaming driver | `stream.validate_streaming.profile_sound`, `profile_total`, and `profile_complete` in [Stream/DriverSound](Itasca/Stream/DriverSound.lean), [DriverTotal](Itasca/Stream/DriverTotal.lean), and [DriverComplete](Itasca/Stream/DriverComplete.lean). |
| Contiguous adapter | [Stream/SliceSound](Itasca/Stream/SliceSound.lean) and [SliceComplete](Itasca/Stream/SliceComplete.lean) discharge the driver contracts for `validate_module`. |
| Worker batches | [Stream/Batch](Itasca/Stream/Batch.lean) and [BatchComplete](Itasca/Stream/BatchComplete.lean): ordered entry validation and exact coverage. |
| Bodies and entries | [Profile/BodyVisitor](Itasca/Profile/BodyVisitor.lean), [EntrySound](Itasca/Profile/EntrySound.lean), and [EntryComplete](Itasca/Profile/EntryComplete.lean) for both profiles, built on [Wasm1/](Itasca/Wasm1) and [Wasm2/](Itasca/Wasm2) `Soundness`, `Totality`, and `Completeness`. |
| Callback traces | [Wasm1/Trace/Body](Itasca/Wasm1/Trace/Body.lean), [Module/Code/EntryTrace](Itasca/Module/Code/EntryTrace.lean), and [Wasm2/Trace/Correspondence](Itasca/Wasm2/Trace/Correspondence.lean). |
| Decoding uniqueness | [Binary/ModuleUnique](Itasca/Binary/ModuleUnique.lean) and [Profile/BinaryUnique](Itasca/Profile/BinaryUnique.lean), without typing or size premises. |

Soundness yields `ModuleSound.Validated`: one raw module that the bytes encode,
that elaborates to a `Module_ok` SpecTec module satisfying the profile, and that
the returned environment, tail, and accessors describe. Completeness assumes
`ModuleEncodingWithinLimits`, `ModuleSignaturesWithinLimits`, `Elaborates`,
`Module_ok`, and `ModuleElaboration.Profile`, and never parser success. Body byte
bounds include the final `end`; local bounds exclude parameters.

### Streaming premises

| Claim | Requires |
| --- | --- |
| Soundness | `StreamSource.Coherent`: successful views agree with fixed logical bytes. `StreamScheduler.Provenance`: returned workers derive from issued seeds through `StreamBatch.Reachable`. |
| Termination | `StreamSource.CallbacksTotal` and `StreamScheduler.CallbacksTotal`: callbacks return. Nothing about the bytes or workers. |
| Completeness | `StreamSource.CanonicalAvailable`: canonical regions are readable. `StreamAcceptingScheduler.Accepts`: positive batch settings, accepting callbacks, and actual `validate_all` results in any order. |

Soundness allows read errors and any split. The driver itself checks pending IDs
and completion, so provenance does not assume workers finish. The accepting
scheduler is one sufficient policy, not the only one. Logical coherence across
separate source calls remains the embedding's obligation.

### Traces

Body traces identify operator hooks, their order, state snapshots, and
immediates (float bits, branch-table labels, block signatures, and SIMD
immediates). Wasm 1.0 entry traces also cover the function-start callback. An
observed rejecting callback is included and is last. Traces cover only
executions that return; they do not specify full traces of rejected modules or
an exact error for every malformed input.

## Proof architecture

The directories below are layered top to bottom. `just prove` enforces the
foundation: `Support/`, `Spec/`, and `Binary/` import only rows above them, and
`Handler/` adds only `Visitor/`. Above that, the order is a guide.

| Directory | Contents |
| --- | --- |
| `Generated/` | Aeneas models of the Rust validator and the handwritten external models. |
| `Support/` | Result inversion, loop lemmas, dispatch simprocs, and translation of Rust types and `module.Env` into SpecTec contexts. |
| `Spec/` | Checks of and additions to the generated specification: declared references, `Instrs_ok` inversion, constants. |
| `Binary/` | The independent grammar: LEB128, floats, names, modules, uniqueness, and the `Wasm1/` and `Wasm2/` instruction grammars. |
| `Handler/` | Lemmas about individual extracted handlers, and `Realizes`/`TypedPrefix` for stacks. |
| `Visitor/` | Profile-agnostic visitor contracts, erasure, lifting, and the trace framework. |
| `Wasm1/` | Wasm 1.0 bodies: zipper, invariant, steps, results, plus `Complete/`, `Visitor/`, and `Trace/`. |
| `Wasm2/` | Wasm 2.0 bodies, split like the Rust dispatch into `Scalar/`, `NumericExt/`, `References/`, `Bulk/`, `Simd/`, `Control/`, and `Step/`, with the same subdirectories as `Wasm1/`. |
| `Profile/` | Body and entry contracts parametric over the profile. |
| `Module/` | Readers, constant expressions, sections, environment, code entries, elaboration, custom sections, and the public theorems. |
| `Stream/` | Source and scheduler contracts, batches, the driver, and the contiguous adapter. |
| `Examples/` | Kernel-checked examples. |

Within a family, `X` or `XSound` proves soundness or invariant preservation,
`XTotal` termination, and `XComplete` acceptance from independent premises.

Some dependencies run against intuition. The public module theorems build on
`Stream/` because `validate_module` runs through the streaming adapter. Both
profiles share `code.body_loop_loop`; [Wasm1/SharedLoop](Itasca/Wasm1/SharedLoop.lean)
proves it equal at `.Wasm1` to the proof-only
[Wasm1/LegacyExecution](Itasca/Wasm1/LegacyExecution.lean) model. Keep the
independent body contracts in [Wasm2/BodySpec](Itasca/Wasm2/BodySpec.lean) and
[Profile/BodySpec](Itasca/Profile/BodySpec.lean) free of the soundness and
completeness proofs, so grammar and module code can import them cheaply.

## Specification gaps

The proofs supplement the pinned specification without editing it:

- The generated typing omits the `C.refs` condition on `ref.func`.
  [Spec/DeclaredReferences](Itasca/Spec/DeclaredReferences.lean) requires every
  `ref.func` target to occur in the module outside function definitions and the
  start declaration. Module, entry, and body certificates carry it.
- The generated module judgment lacks export-name uniqueness and similar
  conditions, which the profile adds.
- The SpecTec binary table assigns SIMD subopcode 92 to both `v128.load32_zero`
  and `v128.load64_zero`. The grammar and Rust use 92 and 93. The proofs use
  SpecTec typing, not its binary decoding, so no assumption is needed.
- Wasm 1.0 requires `br_table` targets to be equal, which Wasm 2.0 typing does
  not; [Examples/Wasm1/ProfileBoundary](Itasca/Examples/Wasm1/ProfileBoundary.lean)
  shows why.

### Source patches

Build targets apply these to the pinned checkouts:

- [aeneas-lean-extraction.patch](../patches/aeneas-lean-extraction.patch) fixes
  Lean name shadowing and nested branch indentation; `just regressions` checks
  it.
- [spectec-wasm2-global-mutability.patch](../patches/spectec-wasm2-global-mutability.patch)
  keeps both global mutabilities in typing.
- [spectec-wasm2-module.patch](../patches/spectec-wasm2-module.patch)
  disambiguates import projections and fixes the four-byte UTF-8 upper bound.

## Extending the profile

The Wasm 2.0 instruction restriction in
[Profile/Instructions](Itasca/Profile/Instructions.lean) is `True`: the binary
grammar bounds the accepted instructions, so broader SpecTec typing alone
accepts nothing new. Add binary syntax, Rust dispatch, typing preservation, and
completeness together. Keep language restrictions separate from the bounds in
[Profile/Types](Itasca/Profile/Types.lean).

Segment and table instructions cross the module/body boundary.
[Module/Code/BodyContext](Itasca/Module/Code/BodyContext.lean) transports typing
across it, and [Module/Code/BodySyntax](Itasca/Module/Code/BodySyntax.lean)
holds the Wasm 1.0 restriction on them. Changes to tables, value types, segments,
or constant expressions also touch
[Module/Elab/Elaboration](Itasca/Module/Elab/Elaboration.lean),
[Module/Elab/Profile](Itasca/Module/Elab/Profile.lean), and the module grammar.

## Audit

[Audit.lean](Itasca/Audit.lean) checks every declaration from an imported Itasca
module, including private helpers, generated auxiliaries, adapters, and external
models. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
`just trust` sets `ITASCA_AUDIT_VERBOSE=1` to print each declaration's axioms;
the setting changes only the report.

[scripts/check_audit.py](scripts/check_audit.py) checks that `Itasca.Audit`
imports exactly the sink modules of the import graph, that the foundation
layers import only downward, and that nothing imports the external template.
[scripts/check_externals.py](scripts/check_externals.py) compares extraction
requests with the external models. Both run under `just prove` and
`just extract-check`.

Upstream sources contain unfinished lemmas and opaque execution models; the
audit ensures the proofs do not depend on them.

## Execution boundary

The Rust `runtime` module is excluded under `cfg(charon)` and has no
correspondence proof. See the [execution guide](../docs/EXECUTION.md) and the
[numeric extraction gaps](../docs/EXECUTION_NUMERICS.md).
