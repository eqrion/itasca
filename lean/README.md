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
just extract          # Rust -> LLBC -> the validator and runtime Lean model
just extract-check    # Regenerate separately and reject stale models
just check Itasca.Results.Validate  # Build specific modules
just profile Itasca.Wasm2.Step.ScalarContext  # Profile one file's elaboration
just prove            # Build all proofs and check audit coverage and axioms
just dead --check     # Optional: check reachability from headline results and examples
just audit-imports    # Refresh each library's audit imports
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
by hand. One Charon and Aeneas pass extracts the validator and the runtime, so
the runtime calls the validator's definitions directly. Charon runs with
`--cfg=charon`, which excludes only the native platform wrappers.
[FunsExternal.lean](Itasca/Generated/FunsExternal.lean) is the handwritten
model of `Vec.pop`, `Vec.is_empty`, `count_ones` and `trailing_zeros`. The
generated external template is ignored and must not be imported; every request
it lists requires a concrete attributed definition.

[SpecTec/wasm2.0.lean](SpecTec/wasm2.0.lean) is generated from the pinned SpecTec
sources and the patches below, and checked byte for byte by `just spec-check`.
The `SpecTecSupport` library compiles upstream's handwritten
`ExtendedDeriveDecEq.lean`. Neither relies on upstream compiled artifacts.

## Proof contracts

[Itasca/Main.lean](Itasca/Main.lean) lists every headline theorem, and each is
stated in full under [Itasca/Results/](Itasca/Results). `profile_*` theorems
quantify over both `ValidationProfile` values; `wasm_*` corollaries specialize to
Wasm 1.0.

| Layer | Contracts |
| --- | --- |
| Whole module | [Results/Validate](Itasca/Results/Validate.lean): `module.validate_module.profile_total`, `profile_sound`, `profile_spec`, `profile_complete`, `profile_complete_with_metadata`. |
| Streaming driver | [Results/Stream](Itasca/Results/Stream.lean): `stream.validate_streaming.profile_sound`, `profile_total`, and `profile_complete`, proved in [Stream/DriverSound](Itasca/Stream/DriverSound.lean), [DriverTotal](Itasca/Stream/DriverTotal.lean), and [DriverComplete](Itasca/Stream/DriverComplete.lean). |
| Contiguous adapter | [Stream/SliceSound](Itasca/Stream/SliceSound.lean) and [SliceComplete](Itasca/Stream/SliceComplete.lean) discharge the driver contracts for `validate_module`. |
| Worker batches | [Results/Batch](Itasca/Results/Batch.lean): `stream.CodeBatch.validate_func`, `validate_all`, and `finish.sound`, giving ordered entry validation and exact coverage. |
| Bodies and entries | [Profile/BodyVisitor](Itasca/Profile/BodyVisitor.lean), [EntrySound](Itasca/Profile/EntrySound.lean), and [EntryComplete](Itasca/Profile/EntryComplete.lean) for both profiles, built on [Wasm2/](Itasca/Wasm2) `Soundness`, `Totality`, and `Completeness`. |
| Callback traces | [Results/Trace](Itasca/Results/Trace.lean), proved in [Wasm2/Trace/Correspondence](Itasca/Wasm2/Trace/Correspondence.lean) and [Profile/EntryTrace](Itasca/Profile/EntryTrace.lean). |
| Decoding uniqueness | [Results/Unique](Itasca/Results/Unique.lean), built on [Binary/ModuleUnique](Itasca/Binary/ModuleUnique.lean) and [Profile/BinaryUnique](Itasca/Profile/BinaryUnique.lean), without typing or size premises. |

Soundness yields `ModuleSound.Validated`: one raw module that the bytes encode,
that elaborates to a `Module_ok` SpecTec module satisfying the profile, and that
the returned environment, tail, and accessors describe. Completeness assumes
`ModuleEncodingWithinLimits`, `ModuleSignaturesWithinLimits`, `Elaborates`,
`Module_ok`, and `ModuleElaboration.Profile`, and never parser success. Body byte
bounds include the final `end`; local bounds exclude parameters.

### Streaming premises

[Itasca/Contracts.lean](Itasca/Contracts.lean) defines every premise below.

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
`Handler/` adds only `Visitor/`. `Contracts` imports only `Module/` and below.
`Results/` and `Main` sit at the top: only `Main` and `Examples/` import them,
and examples import only `Main`. Between these, the order is a guide.

| Directory | Contents |
| --- | --- |
| `Generated/` | Aeneas models of the Rust validator and runtime, and the handwritten external models. |
| `Support/` | Result inversion, loop lemmas, dispatch simprocs, and translation of Rust types and `module.Env` into SpecTec contexts. |
| `Spec/` | Checks of and additions to the generated specification: declared references, `Instrs_ok` inversion, constants. |
| `Binary/` | The independent grammar: LEB128, floats, names, modules, uniqueness, and the `Wasm1/` and `Wasm2/` instruction grammars. |
| `Handler/` | Lemmas about individual extracted handlers, and `Realizes`/`TypedPrefix` for stacks. |
| `Visitor/` | Profile-agnostic visitor contracts, erasure, lifting, and the trace framework. |
| `Wasm1/` | The Wasm 1.0 restrictions on instruction trees, and completeness lemmas for the instructions both profiles share. |
| `Wasm2/` | Function bodies for both profiles, split like the Rust dispatch into `Scalar/`, `NumericExt/`, `References/`, `Bulk/`, `Simd/`, `Control/`, and `Step/`, plus `Complete/`, `Visitor/`, and `Trace/`. The `Profile*` files state the Wasm 1.0 filters and relate the two profiles. |
| `Profile/` | Body and entry contracts parametric over the profile. |
| `Contracts` | Definitions of the streaming source, scheduler, and worker obligations. |
| `Module/` | Readers, constant expressions, sections, environment, code entries, elaboration, and custom sections. |
| `Stream/` | Sources, scheduler proofs, batches, the driver, and the contiguous adapter. |
| `Runtime/` | Source semantics and machine, representation/platform contracts, compiler, interpreter, store, and API integration proofs; see the [execution proof guide](Itasca/Runtime/README.md). |
| `Results/` | The headline theorems, each a projection of its internal construction. |
| `Main` | The entry module, listing every headline theorem. |
| `Examples/` | Kernel-checked examples, using the results through `Main`. |

Within a family, `X` or `XSound` proves soundness or invariant preservation,
`XTotal` termination, and `XComplete` acceptance from independent premises.

Some dependencies run against intuition. The whole-module results build on
`Stream/` because `validate_module` runs through the streaming adapter. Both
profiles share `code.body_loop_loop`; at `.Wasm1` it filters each step
([Wasm2/ProfileFilters](Itasca/Wasm2/ProfileFilters.lean)) before running the
Wasm 2.0 rules, and [Wasm2/ProfileAgreement](Itasca/Wasm2/ProfileAgreement.lean)
shows a Wasm 1.0 run matches the Wasm 2.0 run unless a filter rejects. Keep the
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
- [spectec-wasm2-hostfunc.patch](../patches/spectec-wasm2-hostfunc.patch)
  introduces explicit host function codes for the execution extension.
- [spectec-wasm2-host-typing.patch](../patches/spectec-wasm2-host-typing.patch)
  adds function-instance typing for host code with a valid signature and a
  well-formed module representation, without a Wasm body. The source lemmas in
  [Runtime/Spec/Typing/HostTyping](Itasca/Runtime/Spec/Typing/HostTyping.lean) construct a typed host-only
  store using the decoder's empty module environment and recover exactly the
  original premises for Wasm function instances. This extends the execution
  typing target; it does not establish callback store-typing preservation.
- [spectec-wasm2-lane-store.patch](../patches/spectec-wasm2-lane-store.patch)
  checks lane stores in bytes and adds an explicit success bound. Generated
  memory splicing alone does not enforce that bound. General guard partition
  and boundary lemmas in [Runtime/Spec/Simd/MemoryLaneStore](Itasca/Runtime/Spec/Simd/MemoryLaneStore.lean)
  cover all supported widths and unbounded effective addresses. This repairs
  the execution target without changing validator typing or runtime behavior.
- [spectec-wasm2-memory-write-bounds.patch](../patches/spectec-wasm2-memory-write-bounds.patch)
  requires the shared source memory update to stay within the original byte
  range. This covers scalar, packed, vector and bulk stores as well as lanes.
  Concrete bulk-write helpers require destination bounds obtained from their
  enclosing source operation.
- [spectec-wasm2-export-membership.patch](../patches/spectec-wasm2-export-membership.patch)
  keeps membership inside per-export iteration, avoiding a generated global
  nonempty-namespace premise on empty exports. The source membership judgment
  is characterized in [Runtime/Spec/ModuleMembership](Itasca/Runtime/Spec/ModuleMembership.lean).
  This changes execution instance typing without changing validator typing.
- [spectec-wasm2-load-value-bounds.patch](../patches/spectec-wasm2-load-value-bounds.patch)
  bounds words decoded by packed scalar and widening SIMD loads before
  extension. Byte equality alone truncates higher bits and admitted distinct
  results. [Runtime/Spec/ByteEncoding](Itasca/Runtime/Spec/ByteEncoding.lean) proves bounded
  decoding is unique. This repairs execution rules without changing
  validator typing or runtime decoding.
- [spectec-wasm2-integer-domains.patch](../patches/spectec-wasm2-integer-domains.patch)
  makes integer division/remainder success exclude zero divisors and signed
  division overflow. Without these explicit source guards, the generated
  relations overlap trapping clauses because Lean rational division is total.
  The checked `division_zero_only` and `remainder_zero_only` lemmas in
  [Runtime/Spec/IntegerDiv](Itasca/Runtime/Spec/IntegerDiv.lean) prevent that overlap from
  returning. This repairs the execution specification; validator typing rules
  are unchanged.
- [spectec-wasm2-memory-boundary.patch](../patches/spectec-wasm2-memory-boundary.patch)
  uses 32-bit addition for recursive bulk-memory successor addresses. This
  repairs the invalid `i32.const 2^32` reached after writing the last byte of
  a 4 GiB memory. Bounds checks remain unbounded; only a final zero-count
  iteration can observe the wrapped address. This changes the trusted execution
  target without changing validator typing rules or runtime behavior.

## Extending the profile

The Wasm 2.0 instruction restriction in
[Profile/Instructions](Itasca/Profile/Instructions.lean) is `True`: the binary
grammar bounds the accepted instructions, so broader SpecTec typing alone
accepts nothing new. Add binary syntax, Rust dispatch, typing preservation, and
completeness together. Keep language restrictions separate from the bounds in
[Profile/Types](Itasca/Profile/Types.lean).

Segment and table instructions cross the module/body boundary.
[Module/Code/BodyContext](Itasca/Module/Code/BodyContext.lean) transports typing
across it. Changes to tables, value types, segments, or constant expressions also
touch
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
layers import only downward, that validator layers never import `Runtime/` or
`SpecExt`, that only `Main` and `Examples/` import `Results/` (runtime proofs
may also use the validator results), that examples import only `Main` (`EXAMPLE_IMPORTS` lists the
exceptions), and that nothing imports the external template.
[scripts/check_externals.py](scripts/check_externals.py) compares extraction
requests with the external models. Both run under `just prove` and
`just extract-check`.

Upstream sources contain unfinished lemmas and opaque execution models; the
audit ensures the proofs do not depend on them.

## Execution boundary

The slot runtime has checked public correspondence, invariant, resource-cause
and progress theorems under explicit platform and callback contracts.
[Main.lean](Itasca/Main.lean) lists every headline theorem, each stated in
full under [Results/](Itasca/Results), and [Runtime/Contracts.lean](Itasca/Runtime/Contracts.lean)
lists every premise an embedder must discharge to use the runtime results. The
[execution proof guide](Itasca/Runtime/README.md) describes how the proofs are assembled.

`SpecExt.Builtins` supplies concrete definitions for all 64 pinned builtin
signatures. Float rounding uses exact rationals and midpoint comparisons; the
NaN sets retain permitted nondeterminism. The audit rejects any new opaque builtin placeholder.

`SpecExt.Host` adds atomic host-call steps with explicit typed inputs/results,
store extension, post-call `Store_ok`, and well-formedness premises. The checked
[decoded-store bridge](Itasca/Runtime/Store/Invariant/SourceStoreTyping.lean) now derives
source store typing from the public API certificate, including host functions,
without adding `Store_ok` as a certificate field. It retains source-name
uniqueness from validation alongside export bounds. Fixed and evolving-world
callback contracts retain the stronger source-typing postcondition, including
traps with committed effects.
`Itasca.Runtime.Spec` provides checked context, depth, extension, and mutation lemmas.
The execution proofs build on these foundations. Allocation/content
preservation and callback normal-return laws are explicit premises, together
with floating-point and memory laws. Host-capable proofs additionally require
raw frame-metadata retention, nondecreasing extern counts, and issued callback
values. These conditions are explicit parts of the indexed host contract; they are
not inferred from decoded source-store extension.

The retained compiler relation distinguishes normal exits from branch targets
and records whether each exit is live. Empty source continuations require a
live normal exit; branches require a live target. Dead scopes therefore need
no certificate for source suffixes that the compiler omits. Outermost live
continuations retain the actual typed Return epilogue, while a dead nonvoid
body may have the compiler's zero-width epilogue. These are syntactic invariant
conditions, not assumptions about machine execution. The complete-profile
compiler body fold is checked for both profiles. Actual construction, entry
validation, and finishing produce a certificate for the independently encoded
source body. The
[complete compilation theorem](Itasca/Results/Compile.lean) combines
all-input normal return with independently encoded complete-profile function,
initializer, metadata and capacity certificates. It has no accepted-body or
opcode-subset premise. [Compiler completeness](Itasca/Results/Compile.lean)
constructs actual successful compilation and that certificate from independent
source validity, conservative source-only `CompileEligible` bounds, allocator
correctness, and bounded allocation availability. The envelope uses uniform
source body/local/operand maxima and aggregates function and initializer costs;
it need not accept every module exactly at a configured output limit.

[Public invocation](Itasca/Results/Invoke.lean) (`behaves`) covers issued Wasm
and host handles. On return it retains the full `ExecutableInv` with the final
code interpretation, proves unchanged-state API rejection, relates returned
values, errors and final stores to source runs that use the actual recorded
event log, and classifies every resource error. Callbacks may diverge. Divergence
yields a coherent infinite source execution, or a source run that reaches a
store on which a callback diverges. `terminates` gives a return when neither
exists.
[Instantiation](Itasca/Results/Instantiate.lean) is total and runs no callback.
It links, allocates and initializes the module, retains rollback before
publication, classifies every resource error, and returns the resolved start
function, which the embedder runs with `invoke_with`. Success reaches the call of
that function in the source instantiation, so instantiate-then-invoke follows
the source module start. [No spurious errors](Itasca/Results/Invoke.lean) shows
that an owned, typed call reports only traps when every source run of the
invocation fits the store's value and frame limits (`SourceResourcesFit`, over
all typed host replies), the allocator grants every request, interrupts
continue, and callbacks keep the store limits and never report stack overflow.
It covers both complete profiles and issued Wasm/host functions; it does not
assert source-step determinism.

The [trapping host example](Itasca/Examples/TrapHost.lean) discharges every host,
interrupt and allocator premise of `no_spurious_errors` with a callback that
traps, continuing interrupts and an allocator that grants every request, so the
callback contracts are satisfiable.

The reviewed [native wrappers](../src/runtime/native.rs) forward compilation,
invocation, instantiation, definitions and growth to the corresponding generic
functions. `StdAlloc` uses `Vec::try_reserve`; its content-preservation and
normal-return laws remain in the Rust allocator boundary. `NativeFloat` uses
native arithmetic/casts and `libm`; its agreement with `FloatOpsCorrect` depends
on the documented floating-point environment. Store construction issues
nonzero identities through checked atomic increments and panics if the identity
space is exhausted. That constructor is outside the extracted no-panic claims
for compilation, invocation and instantiation. None of this wrapper review is a
kernel proof of native Rust, `libm`, allocator or atomic semantics.

Runtime import layers and compiler/invocation integration stages are enforced
by the audit checker, which also rejects import cycles. `Runtime/Compiler/`
keeps Local → Body → Module stages. `Runtime/Interp/Machine/` groups machine
proofs by operations, frames, calls, retention and progress;
`Runtime/Integration/Execution/` assembles ownership, mutation, dispatch,
histories, evolving worlds and resource causes. Shared store decoding and
capacity contracts live below these constructions in `Runtime/Representation/`.
`Runtime/SourceMachine/` retains the flat source transition system independently
of the extracted runtime.

The [execution proof guide](Itasca/Runtime/README.md) gives the enforced layer
map and concrete [compilation](Itasca/Runtime/README.md#compilation),
[invocation](Itasca/Runtime/README.md#invocation), and
[instantiation](Itasca/Runtime/README.md#instantiation) reading paths.
Validator proofs never import `Itasca.Runtime` or `SpecExt`; only `Main` and the
runtime results under `Results/` join the two. Runtime proofs reach generated
functions through `Itasca.Runtime.Equations`. The runtime contract entry point
admits only the exact `Integration.Api.ExecutableInv` module from the integration
layer; it cannot import the constructions that assume those contracts.
