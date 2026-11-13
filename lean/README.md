# Lean verification

Lean checks the extracted Rust validator against SpecTec-generated Wasm 2.0
typing rules and an independent binary grammar for Wasm 2.0.
The [project README](../README.md#formal-verification) states the
public guarantees and trust boundary, and [DEVELOPMENT.md](../DEVELOPMENT.md)
the change workflow. This guide covers setup, proof contracts, and layout. The
[proof engineering guide](PROOF_ENGINEERING.md) explains how to write
maintainable proofs. If you are new to Lean, start with
[A guide to the itasca proofs](PROOF_GUIDE.md).

## Setup

| Component | Pin |
| --- | --- |
| Aeneas | `557eff83ecef5083b98a52a94ca7fae63d6c1dab` |
| Charon | `c8f15d7d658c86a95658f71ad99cddd4be002e04`, from Aeneas's `charon-pin` |
| Rust for Charon | `nightly-2026-09-17` |
| Lean and Mathlib | `v4.31.0` |
| SpecTec | `edc84f7ec81f927f3fdb952a82ecd38fed8e4f29` |
| OCaml and Dune | `5.2.0` and `3.23.1`, in the `itasca-lean` opam switch |

Install Git, make, opam, rustup, elan, and just first. From the repository root:

```sh
git submodule update --init vendor/spectec tests/third_party/wasm-spec

opam switch create itasca-lean ocaml-base-compiler.5.2.0 --no-switch -y
opam install --switch=itasca-lean -y dune.3.23.1 dune-build-info.3.23.1 \
  ocamlformat.0.27.0 calendar core_unix \
  domainslib easy_logging menhir ocamlgraph ppx_deriving ppx_deriving_yojson \
  progress unionFind visitors yojson zarith pprint

rustup toolchain install nightly-2026-09-17 --profile minimal \
  --component rustc-dev,rust-src,llvm-tools
elan toolchain install leanprover/lean4:v4.31.0
just tools
cd lean
lake exe cache get
```

For proof work, install `uv` (`brew install uv`) and register the Lean language
server with the editor you use. From the repository root, these portable
commands set the project root to this checkout's `lean/` directory:

```sh
LEAN_ROOT="$(pwd)/lean"
claude mcp add lean-lsp --env LEAN_PROJECT_PATH="$LEAN_ROOT" -- uvx lean-lsp-mcp
codex mcp add lean-lsp --env LEAN_PROJECT_PATH="$LEAN_ROOT" -- uvx lean-lsp-mcp
```

The server provides Lean goals, diagnostics, and tactic attempts during
iteration. See [Use the language server](PROOF_ENGINEERING.md#use-the-language-server)
for the proof workflow.

Use the committed `lake-manifest.json`; builds do not need `lake update`.
`OPAM_SWITCH` selects another compatible switch. Dune stays at 3.23.1 because
3.24 rejects SpecTec's nested legacy Coq project. SpecTec's own Lake project
selects Lean 4.32, but its generated output compiles here on 4.31.

### Installing and rebuilding extraction tools

`just tools` builds and installs the pinned upstream Aeneas and its matching
Charon into `${XDG_CACHE_HOME:-$HOME/.cache}/itasca/aeneas-<revision>/bin`.
The commands above install the build prerequisites first. No PATH changes are
needed: extraction invokes these installed binaries directly and does not
rebuild them. A missing installation reports `Run just tools`.

The [installer](install-tools.sh) keeps clean source checkouts and incremental
build artifacts under that directory's `source/`. It reads Charon's revision
from Aeneas's `charon-pin`,
builds both Rust executables (`charon` and `charon-driver`), builds Aeneas with
Dune, and copies the three executables into `bin/`. Rerun `just tools` to rebuild;
it refuses modified source checkouts. To relocate the installation, use the same
`TOOLS_CACHE` override for installation and extraction, for example:

```sh
make tools TOOLS_CACHE=/absolute/path/to/tool-cache
make extract-check TOOLS_CACHE=/absolute/path/to/tool-cache
```

If you already have a compatible opam switch, use it with
`make tools OPAM_SWITCH=your-switch` instead of creating `itasca-lean`.

`opam` manages OCaml packages; a switch is an isolated OCaml compiler and package
environment. `dune` is the OCaml build tool. `OPAM_SWITCH` selects the switch used
for source builds (also used to build SpecTec). Charon is built with Cargo and
requires the pinned Rust nightly plus its `rustc-dev`, `rust-src`, and `llvm-tools`
components even after installation.

Lake fetches Aeneas's Lean library as a Git dependency into `.lake/packages/`.
Ordinary proof builds use the committed manifest. To intentionally change Aeneas,
update the matching revisions in [toolchain.mk](toolchain.mk),
[lakefile.lean](lakefile.lean), and the table above, check its `charon-pin` and
Rust toolchain, run `just tools`, then run
`cd lean && lake update aeneas` and review the manifest diff. Run both Cargo test
configurations, `just extract`, `just extract-check`, and `just prove` before
accepting the update. The extractor and Lean library must use the same revision.

## Commands

```sh
just extract          # Rust -> LLBC -> the validator and runtime Lean model
just extract-check    # Regenerate separately and reject stale models
just check Itasca.Results.Validate  # Build specific modules
just profile Itasca.Wasm2.Step.ScalarContext  # Profile one file's elaboration
just prove            # Build every proof module
just lint             # Layering, forbidden constructs, metric ratchet, and links
just audit            # Headline theorem axiom allowlist and statement cone
just spec-update      # Copy a regenerated specification into the source tree
just spec-check       # Regenerate, compare, and compile the specification
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
stated in full under [Itasca/Results/](Itasca/Results). The validator supports Wasm 2.0 directly.

| Layer | Contracts |
| --- | --- |
| Whole module | [Results/Validate](Itasca/Results/Validate.lean): `metadata.validate_module.total`, `sound`, `spec`, `complete`, `complete_with_metadata`. |
| Streaming driver | [Results/Stream](Itasca/Results/Stream.lean): `stream.validate_streaming.sound`, `total`, and `complete`, proved in [Stream/DriverSound](Itasca/Stream/DriverSound.lean), [DriverTotal](Itasca/Stream/DriverTotal.lean), and [DriverComplete](Itasca/Stream/DriverComplete.lean). |
| Contiguous adapter | [Stream/SliceSound](Itasca/Stream/SliceSound.lean) and [SliceComplete](Itasca/Stream/SliceComplete.lean) discharge the driver contracts for `validate_module`. |
| Worker batches | [Results/Batch](Itasca/Results/Batch.lean): `stream.CodeBatch.validate_func`, `validate_all`, and `finish.sound`, giving ordered entry validation and exact coverage. |
| Bodies and entries | [Wasm2/BodySpec](Itasca/Wasm2/BodySpec.lean) defines the `Wasm2.Validated` body certificate; [Profile/BodyVisitor](Itasca/Profile/BodyVisitor.lean), [EntrySound](Itasca/Profile/EntrySound.lean), and [EntryComplete](Itasca/Profile/EntryComplete.lean) cover visiting and entry contracts. |
| Callback traces | [Results/Trace](Itasca/Results/Trace.lean), proved in [Wasm2/Trace/Correspondence](Itasca/Wasm2/Trace/Correspondence.lean) and [Profile/EntryTrace](Itasca/Profile/EntryTrace.lean). |
| Decoding uniqueness | [Results/Unique](Itasca/Results/Unique.lean), built on [Binary/ModuleUnique](Itasca/Binary/ModuleUnique.lean) and [Profile/BinaryUnique](Itasca/Profile/BinaryUnique.lean), without typing or size premises. |

Soundness yields `ModuleSound.Validated`: one raw module that the bytes encode,
that elaborates to a `Module_ok` SpecTec module satisfying the module restrictions, and that
the returned environment, tail, and accessors describe. Completeness assumes
`ModuleEncodingWithinLimits`, `ModuleSignaturesWithinLimits`, `Elaborates`,
`Module_ok`, and `ModuleElaboration.Restrictions`, and never parser success. Body byte
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
immediates). An observed rejecting callback is included and is last. Traces cover only
executions that return; they do not specify full traces of rejected modules or
an exact error for every malformed input.

## Proof architecture

The directories below are layered top to bottom. `just lint` checks the import
layering and forbidden constructs, along with the metric ratchet and links:
`Support/`, `Spec/`, and `Binary/` import only rows above them, and `Handler/`
adds only `Visitor/`. `Contracts` imports only `Module/` and below.
`Results/` and `Main` sit at the top: only `Main` and `Examples/` import them,
and examples import only `Main`. Between these, the order is a guide.

| Directory | Contents |
| --- | --- |
| `Generated/` | Aeneas models of the Rust validator and runtime, and the handwritten external models. |
| `Support/` | Result inversion, loop lemmas, dispatch simprocs, and translation of Rust types and `metadata.Env` into SpecTec contexts. |
| `Spec/` | Checks of and additions to the generated specification: declared references, `Instrs_ok` inversion, constants. |
| `Binary/` | The independent grammar: LEB128, floats, names, modules, uniqueness, and instruction encodings. |
| `Handler/` | Lemmas about individual extracted handlers, and `Realizes`/`TypedPrefix` for stacks. |
| `Visitor/` | Profile-agnostic visitor contracts, erasure, lifting, and the trace framework. |
| `Wasm1/` | Completeness lemmas for the shared scalar instructions. `Binary/Wasm1/` supplies their encodings, which the Wasm 2.0 grammar extends. |
| `Wasm2/` | Wasm 2.0 function body proofs, split like the Rust dispatch into `Scalar/`, `NumericExt/`, `References/`, `Bulk/`, `Simd/`, `Control/`, and `Step/`, plus `Complete/`, `Visitor/`, and `Trace/`. `Wasm2.Validated` is the body certificate. |
| `Profile/` | Wasm 2.0 code-entry encoding and typing (`Entry`, `EntryTyped`, `CodeEncoding`), signature caps, and entry contracts. |
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
`Stream/` because `validate_module` runs through the streaming adapter. The
body loop validates the Wasm 2.0 instruction grammar directly. Keep the
independent body contracts in [Wasm2/BodySpec](Itasca/Wasm2/BodySpec.lean) and
[Profile/BodySpec](Itasca/Profile/BodySpec.lean) free of soundness and completeness
proofs, so grammar and module code can import them cheaply.

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
- The generated specification contains three unproved well-formedness theorems:
  `Step_is_wf`, `Step_read_is_wf`, and `Step_pure_is_wf`. No handwritten
  declaration may use them; `just audit` fails if a declaration in `Itasca/` or
  `SpecExt/` refers to one.
- SpecTec's Lean output contains abstract syntax and typing judgments, but no
  binary byte encoding or decoding grammar. The handwritten grammar in
  [Itasca/Binary/](Itasca/Binary) therefore has no generated binary grammar to
  cross-check against.

### Source patches

Aeneas runs unmodified at the pinned revision. After extraction,
`scripts/strip_source_lines.py` removes Rust line ranges from generated comments,
retaining source filenames and changing no definitions. Private Rust modules use
`metadata` and `wasm_types` to avoid Lean namespace collisions with fields
named `module` and `types`; their files remain `src/module.rs` and `src/types.rs`.
Local binders also avoid namespaces referenced in the same scope, such as
`limits` and `error`.

Build targets apply the source patches to the pinned checkouts and the builtin
patch to generated Lean output:

- [spectec-wasm2-builtins.patch](../patches/spectec-wasm2-builtins.patch)
  patches generated `wasm2.0.lean` with concrete definitions for all 64 pinned
  builtin signatures and their helpers. These definitions are part of the
  trusted specification.
  Supporting correctness lemmas remain ordinary Lean modules in `SpecExt/`.
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

## Extending validation

The accepted instruction language is bounded by the binary grammar. Add binary
syntax, Rust dispatch, typing preservation, and completeness together. Keep
language rules separate from implementation bounds.

Segment and table instructions cross the module/body boundary.
[Module/Code/BodyContext](Itasca/Module/Code/BodyContext.lean) transports typing
across it. Changes to tables, value types, segments, or constant expressions also
touch
[Module/Elab/Elaboration](Itasca/Module/Elab/Elaboration.lean),
[Module/Elab/Profile](Itasca/Module/Elab/Profile.lean), and the module grammar.

## Proof checking

`just prove` compiles every module in `Itasca` and `SpecExt`, including examples.
Lean checks the proof terms. `just lint` checks dependency layering and
forbidden constructs. `just audit` checks the headline theorem axiom allowlist
and reports the statement cone. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted by the project's proof policy.

## Execution boundary

The slot runtime has checked public correspondence, invariant, resource-cause
and progress theorems under explicit platform and callback contracts.
[Main.lean](Itasca/Main.lean) lists every headline theorem, each stated in
full under [Results/](Itasca/Results), and [Runtime/Contracts.lean](Itasca/Runtime/Contracts.lean)
lists every premise an embedder must discharge to use the runtime results. The
[execution proof guide](Itasca/Runtime/README.md) describes how the proofs are assembled.

[spectec-wasm2-builtins.patch](../patches/spectec-wasm2-builtins.patch) supplies
concrete definitions for all 64 pinned builtin signatures directly in the generated
`wasm2.0.lean`. Float rounding uses exact rationals and midpoint comparisons; the
NaN sets retain permitted nondeterminism. The patch includes signature-compatibility
checks, which do not prove agreement with the Wasm prose. The handwritten
definitions are part of the trusted specification.

The Host section of `SpecExt.Builtins` adds atomic host-call steps with explicit typed inputs/results,
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
conditions, not assumptions about machine execution. The complete Wasm 2.0
compiler body fold is checked for Wasm 2.0. Actual construction, entry
validation, and finishing produce a certificate for the independently encoded
source body. The
[complete compilation theorem](Itasca/Results/Compile.lean) combines
all-input normal return with independently encoded complete Wasm 2.0 function,
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
It links, allocates and initializes the module. Rejection before publication
leaves the store unchanged and never reports a trap. Segment traps preserve
completed writes and allocated objects under Wasm 2.0 validation. It
classifies every resource error and returns the resolved start function, which
the embedder runs with `invoke_with`. Success reaches the call of
that function in the source instantiation, so instantiate-then-invoke follows
the source module start. [No spurious errors](Itasca/Results/Invoke.lean) shows
that an owned, typed call reports only traps when every source run of the
invocation fits the store's value and frame limits (`SourceResourcesFit`, over
all typed host replies), the allocator grants every request, interrupts
continue, and callbacks keep the store limits and never report stack overflow.
It covers the complete Wasm 2.0 profile and issued Wasm/host functions; it does not
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

Keep runtime imports within the documented layers and compiler/invocation
integration stages. Lean rejects import cycles. `Runtime/Compiler/`
keeps Local → Body → Module stages. `Runtime/Interp/Machine/` groups machine
proofs by operations, frames, calls, retention and progress;
`Runtime/Integration/Execution/` assembles ownership, mutation, dispatch,
histories, evolving worlds and resource causes. Shared store decoding and
capacity contracts live below these constructions in `Runtime/Representation/`.
`Runtime/SourceMachine/` retains the flat source transition system independently
of the extracted runtime.

The [execution proof guide](Itasca/Runtime/README.md) gives the layer
map and concrete [compilation](Itasca/Runtime/README.md#compilation),
[invocation](Itasca/Runtime/README.md#invocation), and
[instantiation](Itasca/Runtime/README.md#instantiation) reading paths.
Validator proofs never import `Itasca.Runtime` or `SpecExt`; only `Main` and the
runtime results under `Results/` join the two. Runtime proofs reach generated
functions through `Itasca.Runtime.Equations`. The runtime contract entry point
admits only the exact `Integration.Api.ExecutableInv` module from the integration
layer; it cannot import the constructions that assume those contracts.
