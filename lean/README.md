# Lean verification

Lean checks the extracted Rust validator against SpecTec-generated Wasm 2.0
typing rules and an independent binary grammar for Wasm 2.0.
The [project README](../README.md#formal-verification) states the
public guarantees and trust boundary, and [DEVELOPMENT.md](../DEVELOPMENT.md)
the change workflow. This guide covers setup, proof contracts, and layout. The
[proof engineering guide](PROOF_ENGINEERING.md) explains how to write
maintainable proofs. If you are new to Lean, start with
[A guide to the itasca proofs](Itasca/Results/README.md).

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
TOOLS_CACHE=/absolute/path/to/tool-cache just tools
TOOLS_CACHE=/absolute/path/to/tool-cache just extract-check
```

If you already have a compatible opam switch, select it with
`OPAM_SWITCH=your-switch just tools`.

`opam` manages OCaml packages; a switch is an isolated OCaml compiler and package
environment. `dune` is the OCaml build tool. `OPAM_SWITCH` selects the switch used
for source builds (also used to build SpecTec). Charon is built with Cargo and
requires the pinned Rust nightly plus its `rustc-dev`, `rust-src`, and `llvm-tools`
components even after installation.

Lake fetches Aeneas's Lean library as a Git dependency into `.lake/packages/`.
Ordinary proof builds use the committed manifest. To intentionally change Aeneas,
update the matching revisions in [justfile](justfile),
[lakefile.lean](lakefile.lean), and the table above, check its `charon-pin` and
Rust toolchain, run `just tools`, then run
`cd lean && lake update aeneas` and review the manifest diff. Run both Cargo test
configurations, `just extract`, `just extract-check`, and `just prove` before
accepting the update. The extractor and Lean library must use the same revision.

## Commands

The root justfile exposes the Lean recipes from [lean/justfile](justfile).
Run the Lean commands from either directory and run `just verify` from the
repository root.

```sh
just extract          # Rust -> LLBC -> the validator and runtime Lean model
just extract-check    # Regenerate separately and reject stale models
just check Itasca.Results.Validate  # Build specific modules
just profile Itasca.Body.Step.ScalarContext  # Profile one file's elaboration
just prove            # Build every proof module
just audit            # Build proofs, reject sorry dependencies and list axioms
just spec-update      # Copy a regenerated specification into the source tree
just spec-check       # Regenerate, compare, and compile the specification
just verify           # Rust tests and all verification checks
```

Preserve the `.lake/` and `.build/` caches.

## Generated sources

`just extract` uses Aeneas's built-in split to generate
[Types.lean](Itasca/Generated/Types.lean) and
[Funs.lean](Itasca/Generated/Funs.lean) for both the validator and runtime.
Regenerate them from the extraction inputs. Charon runs with
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

[Itasca/Main.lean](Itasca/Main.lean) lists every public theorem, stated in full
under [Itasca/Results/](Itasca/Results). The shared
[definition reading map](Itasca/Results/Definitions/README.md) explains their definitions and premises. The validator supports Wasm 2.0 directly.

| Layer | Contracts |
| --- | --- |
| Whole module | [Results/Validate](Itasca/Results/Validate.lean): `metadata.validate_module.total`, `sound`, `spec`, `complete`, `complete_with_metadata`. |
| Streaming driver | [Results/Stream](Itasca/Results/Stream.lean): `stream.validate_streaming.sound`, `total`, and `complete`, proved in [Stream/Soundness](Itasca/Stream/SubmissionSound.lean), [Totality](Itasca/Stream/RetirementAndFraming.lean), and [Completeness](Itasca/Stream/Completeness.lean). |
| Contiguous adapter | [Stream/Completeness](Itasca/Stream/Completeness.lean) discharges the driver contracts for `validate_module`. |
| Worker batches | [Results/Batch](Itasca/Results/Batch.lean): `stream.CodeBatch.validate_func`, `validate_all`, and `finish.sound`, giving ordered entry validation and exact coverage. |
| Bodies and entries | [Definitions/Validation](Itasca/Results/Definitions/Validation.lean) exposes the `Body.Validated` body certificate; [CodeEntry/Validation](Itasca/CodeEntry/Validation.lean) covers visiting and entry contracts. |
| Callback traces | [Results/Trace](Itasca/Results/Trace.lean), proved in [Body/Trace/Acceptance](Itasca/Body/Trace/BytesDispatch.lean) and [CodeEntry/Trace](Itasca/CodeEntry/Trace.lean). |
| Decoding uniqueness | [Results/Unique](Itasca/Results/Unique.lean), built on [Binary/ModuleUnique](Itasca/Binary/ModuleUnique.lean) and [CodeEntry/Validation](Itasca/CodeEntry/Validation.lean), without typing or size premises. |

Soundness yields `Module.Sound.Validated`: one raw module that the bytes encode,
that elaborates to a `Module_ok` SpecTec module satisfying the module restrictions, and that
the returned environment, tail, and accessors describe. Completeness assumes
`ModuleEncodingWithinLimits`, `ModuleSignaturesWithinLimits`, `Elaborates`,
`Module_ok`, and `Module.Elaboration.Restrictions`, and never parser success. Body byte
bounds include the final `end`; local bounds exclude parameters.

### Streaming premises

[streaming interface](Itasca/Results/Definitions/Streaming.lean) links the definitions of every premise below.

| Claim | Requires |
| --- | --- |
| Soundness | `Stream.Source.Describes`: successful views agree with regions of one fixed module byte string. `Stream.Scheduler.Provenance`: returned workers derive from issued seeds through `Stream.Batch.Reachable`. |
| Termination | `Stream.Source.CallbacksTotal` and `Stream.Scheduler.CallbacksTotal`: callbacks return. Nothing about the bytes or workers. |
| Completeness | `Stream.Source.CanonicalAvailable`: canonical regions are readable. `Stream.Scheduler.Accepts`: positive batch settings, accepting callbacks, and actual `validate_all` results in any order. |

Soundness allows read errors and any split. The driver itself checks pending IDs
and completion, so provenance does not assume workers finish. The accepting
scheduler is one sufficient policy, not the only one. It accepts bounded issued
work and returns actual worker results, including validation errors, without
assuming Wasm validity. The completeness proof establishes valid batch contents
and successful finishing internally. The outstanding queue permits any completion
order. Logical coherence across separate source calls remains the embedding's
obligation.

### Traces

Body traces identify operator hooks, their order, state snapshots, and
immediates (float bits, branch-table labels, block signatures, and SIMD
immediates). An observed rejecting callback is included and is last. Traces cover only
executions that return; they do not specify full traces of rejected modules or
an exact error for every malformed input. The four public results share the
`Records visitor observe` observation contract. Logging adapters and concrete
recorder corollaries are checked in Visitor and Body/Trace/Acceptance rather
than included in the public statement vocabulary.

## Proof architecture

The public reading surface is [Results](Itasca/Results/README.md) and the named
external foundations. Its [Definitions](Itasca/Results/Definitions/README.md)
contain the complete transitive handwritten statement vocabulary in 15 semantic
units; the nine theorem modules state the guarantees. The
[namespace policy](NAMESPACES.md) aligns semantic subjects across definition and
proof owners. Organizational directories do not add namespace prefixes, and
extracted and upstream operation identities remain unchanged.

Definition modules import only other public definitions, the extracted model,
generated SpecTec and SpecExt foundations, and upstream libraries. They never
import handwritten implementation proofs. Theorem modules may import definitions
and implementation proofs, but their statement vocabulary must stay within the
definition layer and named foundations. Implementation proofs may import narrow
definition modules; they cannot import public theorem modules or Main. Theorem
modules do not import one another. Only Main, examples and external consumers
use the full `Itasca.Results.Definitions` umbrella. Review import changes and
transitive theorem statement dependencies against these boundaries.

Support, Spec and Binary retain their foundation proof restrictions and may use
narrow public definitions. Handler additionally uses Visitor and narrow
public definitions. Validator implementations and the Validation, Streaming
and Callbacks entries must stay independent of Runtime proof modules and
SpecExt, and may depend only on validator functions in the shared `Funs.lean`.
Compiler stages are Local → Body → Module for implementation and definition
owners. Keep compiler declarations independent of interpreter operations.

| Directory | Contents |
| --- | --- |
| `Generated/` | Extracted Rust models and the handwritten trusted external model. |
| `Results/Definitions/` | Public grammar, certificates, effects, representations, source vocabulary and premises. |
| `Results/Definitions/README.md` | Reading paths through the 15 semantic units and the Results theorem groups. |
| `Support/` | Result, loop, translation and dispatch support proofs. |
| `Spec/` | Generated-rule checks, inversion and declared-reference proofs. |
| `Binary/` | Correctness and uniqueness of the independent byte grammar. |
| `Handler/` | Extracted handler contracts and preservation proofs. |
| `Visitor/` | Visitor contracts, erasure, lifting and trace proofs. |
| `Body/` | Wasm 2.0 body, dispatch, preservation, completeness and trace proofs. |
| `CodeEntry/` | Code-entry encoding, typing, visitor and uniqueness proofs. |
| `Module/` | Environment, code, tail, elaboration and section-reader proofs. |
| `Stream/` | Source/scheduler proofs, issued batches, driver and contiguous adapter. |
| `Runtime/` | Compiler, interpreter, store, source-machine and API construction proofs; see the [internal runtime guide](Itasca/Runtime/README.md). |
| `Results/*.lean` | Public theorem statements and their short construction proofs; `Definitions.lean` is the vocabulary umbrella. |
| `Main` | Joins public definitions, all nine theorem modules and checked witnesses. |
| `Examples/Runtime.lean` | Kernel-checked uses of the public results through Main. |

Within a proof family, X or XSound proves soundness or preservation, XTotal
normal return, and XComplete acceptance from independent premises. The
one-contract-per-extracted-function rule concerns implementation proofs;
public semantic placement takes precedence over mirroring Rust files.

Whole-module results build on Stream because validate_module uses the streaming
adapter. The independent body and entry vocabulary is in
[Definitions/Validation](Itasca/Results/Definitions/Validation.lean).
The mutable validator stack model and body-state zipper live in Handler and
Body alongside their construction proofs. They are not public validity premises.

## Specification gaps

The proofs supplement the pinned specification without editing it:

- The generated typing omits the `C.refs` condition on `ref.func`.
  [declared-reference definitions](Itasca/Results/Definitions/Binary.lean) require every
  `ref.func` target to occur in the module outside function definitions and the
  start declaration. Module, entry, and body certificates carry it.
- The generated module judgment lacks export-name uniqueness and similar
  conditions, which the module restrictions add.
- The SpecTec binary table assigns SIMD subopcode 92 to both `v128.load32_zero`
  and `v128.load64_zero`. The grammar and Rust use 92 and 93. The proofs use
  SpecTec typing, not its binary decoding, so no assumption is needed.
- The generated specification contains three unproved well-formedness theorems:
  `Step_is_wf`, `Step_read_is_wf`, and `Step_pure_is_wf`. No handwritten
  declaration may use them. `just audit` fails when a declaration in `Itasca` or
  `SpecExt` inherits their dependency on `sorryAx`.
- SpecTec's Lean output contains abstract syntax and typing judgments, but no
  binary byte encoding or decoding grammar. The handwritten grammar in
  [public binary grammar](Itasca/Results/Definitions/README.md) therefore has no generated binary grammar to
  cross-check against.

### Source patches

Aeneas runs unmodified at the pinned revision. After extraction, the recipe
strips Rust line ranges from generated comments and retains source filenames.
Private Rust modules use
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
  [Runtime/Spec/HostTyping](Itasca/Runtime/Spec/TypingAndNumericOperations.lean) construct a typed host-only
  store using the decoder's empty module environment and recover exactly the
  original premises for Wasm function instances. This extends the execution
  typing target; it does not establish callback store-typing preservation.
- [spectec-wasm2-lane-store.patch](../patches/spectec-wasm2-lane-store.patch)
  checks lane stores in bytes and adds an explicit success bound. Generated
  memory splicing alone does not enforce that bound. General guard partition
  and boundary lemmas in [Runtime/Spec/Simd/MemoryAndFloatOperations](Itasca/Runtime/Spec/Simd/ArithmeticMemoryAndFloat.lean)
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
  is characterized in [Runtime/Spec/ModuleMembership](Itasca/Runtime/Spec/PrimitiveOperations.lean).
  This changes execution instance typing without changing validator typing.
- [spectec-wasm2-load-value-bounds.patch](../patches/spectec-wasm2-load-value-bounds.patch)
  bounds words decoded by packed scalar and widening SIMD loads before
  extension. Byte equality alone truncates higher bits and admitted distinct
  results. [Runtime/Spec/ScalarOperations](Itasca/Runtime/Spec/PrimitiveOperations.lean) proves bounded
  decoding is unique. This repairs execution rules without changing
  validator typing or runtime decoding.
- [spectec-wasm2-integer-domains.patch](../patches/spectec-wasm2-integer-domains.patch)
  makes integer division/remainder success exclude zero divisors and signed
  division overflow. Without these explicit source guards, the generated
  relations overlap trapping clauses because Lean rational division is total.
  The checked `division_zero_only` and `remainder_zero_only` lemmas in
  [Runtime/Spec/IntegerAndSegmentOperations](Itasca/Runtime/Spec/TypingAndNumericOperations.lean) prevent that overlap from
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
[Module/Code/ContextTransport](Itasca/Module/Code/ContextTransport.lean) transports typing
across it. Changes to tables, value types, segments, or constant expressions also
touch
[Module/Elab/ToTyping](Itasca/Module/Elab/ToTyping.lean) and the module grammar.

## Proof checking

`just prove` compiles every module in `Itasca` and `SpecExt`, including examples.
Lean checks the proof terms. `just audit` builds those modules, rejects any
declaration in `Itasca` or `SpecExt` that depends on `sorryAx`, and prints the
axioms those declarations use. The project's proof policy permits only
`propext`, `Classical.choice`, and `Quot.sound`.

## Execution boundary

The slot runtime has checked public correspondence, invariant
and progress theorems under explicit platform and callback contracts.
[Main.lean](Itasca/Main.lean) lists every headline theorem, each stated in
full under [Results/](Itasca/Results). The shared
[public definitions](Itasca/Results/Definitions/README.md), especially Platform, Compilation, Store,
Invocation and Instantiation, exposes the premises an embedder must discharge. The
[execution proof guide](Itasca/Runtime/README.md) describes how the proofs are assembled.

[spectec-wasm2-builtins.patch](../patches/spectec-wasm2-builtins.patch) supplies
concrete definitions for all 64 pinned builtin signatures directly in the generated
`wasm2.0.lean`. Float rounding uses exact rationals and midpoint comparisons; the
NaN sets retain permitted nondeterminism. The patch includes signature-compatibility
checks, which do not prove agreement with the Wasm prose. The handwritten
definitions are part of the trusted specification.

`SpecExt.Host` adds atomic host-call steps with explicit typed inputs/results,
store extension, post-call `Store_ok`, and well-formedness premises. The checked
[decoded-store bridge](Itasca/Runtime/Store/Invariant/CoreInstantiationSource.lean) now derives
source store typing from the internal API certificate, including host functions,
without adding `Store_ok` as a certificate field. It retains source-name
uniqueness from validation alongside export bounds. Fixed and evolving-world
callback contracts retain the stronger source-typing postcondition, including
traps with committed effects.
`Itasca.Spec` provides checked context, depth, extension, and mutation lemmas.
The execution proofs build on these foundations. Allocation/content
preservation and callback normal-return laws are explicit premises, together
with floating-point and memory laws. Host-capable proofs additionally require
raw frame-metadata retention, nondecreasing extern counts, and issued callback
values. These conditions are explicit parts of the indexed host contract; they are
not inferred from decoded source-store extension.

The [store API results](Itasca/Results/Store.lean) cover fresh-store creation,
definitions, writes, growth and reads. `with_identity` establishes
the chosen abstract store predicate when its identity is positive; mutating
operations preserve it under their stated premises. `Integration.runtime_verified`
proves that a predicate satisfying the entire `RuntimeContract` exists. Clients
choose it once and retain it across operations and host callbacks. These include `AllocCorrect` for
allocation-backed definitions and table growth, `MemoryLaws` for memory
operations, issued handles and values, and same-length writeback for
`memory_mut`. Value-type checks reject incompatible inputs without changing
the store. Instantiation and invocation preserve
the invariant under their existing premises. Read results agree with the
corresponding decoded objects; `export` describes the decoded module instance,
while `extern_identity` returns the value in the raw extern identity vector.

The proofs establish generic runtime contracts. They do not prove that the
native identity counter, allocator, memory buffer or floating-point wrapper
satisfies those contracts. Host callbacks establish `HostLaws` through one `HostReturn` postcondition:
retain code meanings and runtime capabilities, extend the typed source store,
preserve issued identities, and return issued values. Store API results support
these callback-specific proofs. Decoded source extension alone does not establish
concrete identity retention. These obligations apply even when the host reports
an error; divergence is permitted and termination is a separate premise.

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
all-input normal return with an independently encoded, typed Wasm 2.0 source
module and matching metadata. Function, initializer and capacity certificates
remain internal. The runtime protocol connects accepted compilation to
instantiation and execution. It has no accepted-body or
opcode-subset premise. [Compiler completeness](Itasca/Results/Compile.lean)
constructs actual successful compilation and that certificate from independent
source validity, `CompileEligible` comparisons against the computed
`compilationBudget`, allocator
correctness, and bounded allocation availability. The envelope uses uniform
source body/local/operand maxima and aggregates function and initializer costs.
Preparation bounds body size by the smaller of the module byte length
and the supported body-size cap. It adds each signature's parameters to the
declared-local cap and allows 500 operand values per allowed body byte. These
are sufficient bounds, not measured stack peaks. The
public premises refer directly to source metadata and configured limits; chosen
validator logs, parser-state certificates, initial schedulers and budget counters
remain internal to the proof. Eligibility does not depend on the allocator's
state type. Its metadata premise is the independent source correspondence,
not a certificate of successful parser calls. It need not accept every module
exactly at a configured output limit.

[Public invocation](Itasca/Results/Invoke.lean) (`behaves`) covers issued Wasm
and host handles. On return it retains the chosen store predicate with the final
code interpretation, proves unchanged-state API rejection, relates returned
values, errors and final stores to source runs that use the actual recorded
event log. Resource exhaustion and interruption retain a reachable source store;
private allocation causes and capacity models are not public obligations. Callbacks
may diverge. Divergence
yields a coherent infinite source execution, or a source run that reaches a
store on which a callback diverges. `terminates` gives a return when neither
exists.
[Instantiation](Itasca/Results/Instantiate.lean) is total and runs no callback.
It links, allocates and initializes the module. Rejection before publication
leaves the store unchanged and never reports a trap. Segment traps preserve
completed writes and allocated objects under Wasm 2.0 validation. It
returns the resolved start function, which the embedder runs with `invoke_with`.
Success reaches that function's call in the source instantiation. Invocation resource
completeness is a separate guarantee: `resource_complete` excludes every error
except a source trap under owned, typed arguments, conservative
[source budgets](Itasca/Results/Definitions/Resources.lean), and embedding
availability. Its divergence-permitting conclusion combines with `terminates`
for ordinary return. Detailed capacity and allocation causes stay internal;
instantiation has no corresponding resource-completeness promise.

The [trapping host example](Itasca/Examples/Runtime.lean) demonstrates satisfiable
host, interrupt and allocator contracts using a callback that traps, continuing
interrupts and an allocator that grants every request.

The same example establishes a fresh executable store and discharges the empty
module's compiler eligibility before applying instantiation. The extracted
[vector memory](Itasca/Runtime/Platform/VecMemory.lean) satisfies all memory laws
under allocator correctness. A [mathematical float dictionary](Itasca/Runtime/Platform/FloatWitness.lean)
satisfies all 27 float contracts by selecting permitted specification results.

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
histories, evolving worlds and resource causes. Shared store decoding lives in Results/Definitions/Representation. Internal
capacity definitions and their proofs live in Runtime/Representation. Public
source execution uses SpecTec configurations and SpecExt host steps directly;
the flat source-machine states, transitions, simulation and progress remain in
Runtime/SourceMachine, independently of the extracted runtime.

The [execution proof guide](Itasca/Runtime/README.md) gives the layer
map and concrete [compilation](Itasca/Runtime/README.md#compilation),
[invocation](Itasca/Runtime/README.md#invocation), and
[instantiation](Itasca/Runtime/README.md#instantiation) reading paths.
All public statement vocabulary lives in Results/Definitions; Runtime remains an internal
implementation directory. Validator proofs must not import Runtime implementation
modules or SpecExt, including through public definitions. `Itasca.Runtime.Equations.Bytecode`
and `.Interp` provide equation lemmas for runtime proofs. Compiler proofs and
their public-definition owners stay independent of interpreter operations. No
handwritten implementation module may occur below public definitions, regardless
of its namespace.
