# Execution verification

The generic slot runtime has kernel-checked compilation, invocation,
instantiation, API invariant, resource-cause, and progress theorems for both
supported profiles. These guarantees are conditional on the platform and
callback contracts below. The [public trust boundary](../README.md#trust-boundary)
and [proof architecture](../lean/Exec/README.md) describe their context.

## Scope

Execution correspondence is forward soundness: a returned runtime result has
an execution in the source semantics. It does not establish source uniqueness
or exhaust the specification's nondeterminism. Compiler completeness is not
proved. Native wrappers and native platform implementations remain reviewed
boundaries outside extraction.

The source store is decoded from concrete objects and a `CodeInterpretation`.
This ghost interpretation maps an instance index, compiled module, and function
index to a source body. Compilation constructs the source certificate;
publication and callbacks may extend the interpretation while retaining every
previously issued key. The interpretation contains no assumed execution proof.
`ExecutableInv` bundles API invariants, segment accounting, and function
capacities under that interpretation.

## Public theorem map

The linked Lean statements are authoritative about quantification and premises.

| Obligation | Checked public scope and premises | Trust boundary and scope |
| --- | --- | --- |
| T1 compilation | [`compile_correct`](../lean/Exec/Theorems/Compilation.lean) jointly proves all-input normal return and a single source-indexed `ModuleCodeRel` certificate, including complete-profile functions, initializers, metadata and capacities, under `AllocCorrect` alone. | The theorem covers both complete profiles without an instruction-subset premise. Native compile wrappers directly instantiate these generic functions; their allocator implementation remains in the reviewed native boundary. |
| T2 instantiation | [The all-bytes world recorder package](../lean/Exec/Theorems/Instantiation/InstantiateExecutableWorldRecordedCompiled.lean) derives the canonical raw module from actual compilation. [The public instantiation resource theorem](../lean/Exec/Theorems/Instantiation/InstantiateExecutableWorldRecordingResources.lean) retains one final interpretation, full invariant, old-key agreement, raw prefix, `Extend_store`, exact rollback, actual recorded events and initialization/start causes. [Actual world divergence](../lean/Exec/Theorems/Instantiation/InstantiateExecutableWorldInfinite.lean) yields coherent infinite source execution. | Requires the indexed callback contract and native platform laws. |
| T3 invocation | [Issued world invocation](../lean/Exec/Theorems/Invocation/PublicExecutableWorldInvocation.lean) covers Host/Wasm source results and errors with one selected final interpretation, full invariant preservation and issued results. [Source-free safety](../lean/Exec/Theorems/Invocation/PublicExecutableWorldSafety.lean) handles every issued handle and argument list without a `fun_invoke` or typing premise, including absent foreign indices. [Public exact recording](../lean/Exec/Theorems/Invocation/PublicExecutableWorldRecorded.lean) relates the public API, its actual recorder graph and the same source event list. | Embedder callbacks must satisfy A2/A7, including normal return and raw metadata retention. |
| T4 safety and causes | [Compilation](../lean/Exec/Code/Module/CompileTotal.lean) returns normally for arbitrary bytes. [Public world invocation](../lean/Exec/Theorems/Invocation/PublicExecutableWorldResources.lean) and [instantiation](../lean/Exec/Theorems/Instantiation/InstantiateExecutableWorldRecordingResources.lean) retain exact public API/recorder graphs, source outcomes, and classified setup, readback, callback, precommit, initializer and start witnesses. Requests at newly published functions use their actual reached interpretation and capacity ledger. [Invocation Objects exclusion](../lean/Exec/Theorems/Invocation/PublicInvocationNoObjects.lean) rules out that impossible public invocation result. | Checked under the distinction between decoded invocation bounds and exact persistent-instantiation accounting. No decoded-store-only projection of the instance registry is claimed. |
| T5 API rejection | [World-aware typed arguments](../lean/Exec/Theorems/Invocation/PublicExecutableWorldTyped.lean) exclude BadArguments; foreign issued references may still produce WrongStore. [World-aware typed imports](../lean/Exec/Theorems/Instantiation/InstantiateExecutableWorldNoLink.lean) exclude Link. [Growth causes](../lean/Exec/Store/Api/ApiGrowSourceCauses.lean) retain declared/configured/intrinsic bounds and actual refusals. | Checked with the intrinsic ceilings. Maximal-table zero-growth success remains separate from failure. |
| T6 API invariant | [`ExecutableInv`](../lean/Exec/Theorems/Api/ExecutableInv.lean) bundles the API certificate, segment accounting and function capacities. Checked constructors, definitions, issued reads/writes/grows, exports and memory borrows preserve it. World-aware public invocation and instantiation retain that same indexed invariant, raw prefixes and cross-world source extension. Fresh interpretation choices agree on all previously issued instance keys. | Checked for the public API under the callback/raw-retention premises. Returned-action composition does not establish those premises for arbitrary callback code. |
| T7 progress | [Actual world finite prefixes](../lean/Exec/Theorems/Progress/ExecutableWorldFinite.lean) and [prepared public prefixes](../lean/Exec/Theorems/Invocation/PublicExecutableWorldFinite.lean) retain the uniform `n / (2 * U32.max + 3)` source bound without an initial/future source-size premise or assumed per-step simulation. [Public world invocation divergence](../lean/Exec/Theorems/Invocation/PublicExecutableWorldDivergence.lean) and world instantiation divergence yield coherent infinite source execution. [Recorded infinite prefixes](../lean/Exec/Theorems/Progress/ExecutableWorldRecordedInfinite.lean) retain exact source labels. | Checked under callback normality. Atomic direct-call traces remain distinct from separate reentrant API traces; finite nesting depth alone does not make a nested divergent invocation return. |

## Outcomes and resource accounting

**T1. Compilation.** If `compile(bytes, profile, limits) = Ok(exe)`, then:

- `Accepts bytes profile m` for some `m`;
- `CodeRel m exe` holds.

Later theorems speak about this `m`.

**T2. Instantiation.** Assume `Inv st` and `instantiate(st, exe, imports, P) = r`,
with resulting store `st'`. Then `Inv st'` holds, and:

- **`Ok(inst)`:** `fun_instantiate (decodeStore st) m (decode imports) c0` holds,
  and `StepsH c0 c1`, where `c1` is the completed config. `c1`'s store is
  `decodeStore st'`, and `inst` decodes to its module instance. The start
  function is included.
- **`Err(Trap t)`:** `StepsH c0` reaches `TRAP`, with store `decodeStore st'`.
  Wasm 2.0 segment writes made before the trap are kept, as the spec requires.
- **Wasm 1.0 out-of-bounds segment:** the result is an error, and
  `decodeStore st' = decodeStore st`. This is the handwritten 1.0 statement in
  `SpecExt/Wasm1.lean`.
- **`Err(Link _)` or `Err(WrongStore)`:** the store is unchanged.
  Private issued handles may belong to another store; issuance alone does not
  establish ownership by the receiving store.
- **`Err(Exhausted _)` before publication:** the decoded store is unchanged.
- **`Err(Exhausted _)` or `Err(Terminated)` after publication:** some `c`
  satisfies `StepsH c0 c`, and its store is `decodeStore st'`. Initialization
  and start-function effects already performed are retained.

The host-event clause from T3 also applies to the start function.

**T3. Invocation.** Assume `Inv st` and
`invoke(exec, st, P, f, args, results) = r`, with resulting store `st'`. Let
`c0` satisfy `fun_invoke (decodeStore st) f (decodeVals args) c0`. Then
`Inv st'` holds, and:

- **`Ok`:** `StepsH c0 (config (decodeStore st', _) (vals (decodeVals results)))`.
- **`Err(Trap _)`:** `StepsH c0 (config (decodeStore st', _) [TRAP])`.
- **`Err(Terminated)` or `Err(Exhausted _)`:** some `c` satisfies `StepsH c0 c`,
  and `c`'s store is `decodeStore st'`.
- **`Err(BadArguments)` or `Err(WrongStore)`:** `st' = st`.
- **Host events:** the label sequence of the `StepsH` run equals the host-call
  log recorded by `Recording P` for this invocation. The log covers function
  address, arguments, and the type-checked results or trap. Reentrant invocations
  have their own logs: the atomic outer host step subsumes their store effects.

The theorem holds for every `P` satisfying the premises in [Platform and callback contracts](#platform-and-callback-contracts).
The allocator and hooks obey their content-preservation and normal-return laws;
their allocation and interrupt decisions remain unrestricted.

**T4. Safety and bounded escape hatches.**
- Under the invariant, issued-input and platform premises of the corresponding
  theorem, extracted `invoke`, `instantiate`, and `compile` never panic. This
  rules out overflow, out-of-bounds indexing and failed unwraps.
- Invocation `Exhausted` results retain one of these causes:
  - `Alloc::reserve` returned false for a request bounded by decoded signature
    buffers or the source frame's validated storage needs;
  - the decoded config's `FRAME_` nesting depth reached the configured frame
    limit;
  - public parameter/result buffers exceed `StoreLimits::max_values`, using
    the larger decoded signature width even before a Wasm frame is entered;
  - the required storage for decoded active call frames exceeds `max_values`:
    locals plus maximum validated operand-stack width, sharing caller argument
    storage with the callee (one slot per scalar/reference, two per vector).
    Host calls require the larger decoded parameter/result width at the
    caller's argument position, including direct calls with no Wasm frame;
  - a host hook returned `HostError::StackOverflow`.
  Invocation does not return `Exhausted(Objects)`.
- Instantiation additionally permits documented preparation/initialization
  failures: configured persistent store quotas (including instance, instance-item,
  object, table-element and memory-byte accounting), an actual refused reserve
  or `MemoryBuffer::new_zeroed` request, and the implementation address-size
  guards needed to represent those requests. The witness retains the actual
  reached preparation phase, compiled module/declaration, request and relevant
  configured bound or guard. Before publication, failure rolls back; after
  publication, initialization/start effects remain as described in T2.
- `Terminated` is returned only after `Platform::interrupt` returned `Terminate`.

Invocation storage/depth causes use decoded source signatures and validated
frame capacities. Persistent instantiation accounting is a separate resource
policy over issued runtime registries and aggregate counters retained by `Inv`;
the decoded Wasm store does not contain the runtime instance registry. Exact
preparation-request witnesses are not claimed to be an independent projection
of every internal count from the decoded store alone.

**T5. Rejection completeness at the API.**
- `invoke` never returns `BadArguments` for arguments that are well-typed
  against `f`'s type in `decodeStore st`.
- `instantiate` never returns `Link` when the imports satisfy the spec's
  `Externaddr_ok` typing.
- `memory.grow`/`table.grow` return failure only if one of these holds:
  - `MemoryBuffer::grow` or `Alloc::reserve` returned false;
  - the declared maximum would be exceeded;
  - the intrinsic Wasm ceiling would be exceeded (65,536 memory pages or the
    u32 table-size bound);
  - a `StoreLimits` bound would be exceeded.

Grow failure here means taking the failure branch. The numeric `table.grow`
result alone cannot distinguish failure from successful growth by zero when
the old table length is `u32::MAX`: both return `0xffffffff`, as the specification
requires. A failure-cause characterization phrased solely in terms of that
sentinel includes this successful boundary case. The unchanged-store guarantee
holds uniformly for the sentinel: appending zero elements at that boundary
also preserves the exact store.

**T6. API invariants.** Every public `Store` function preserves `Inv`. Every
mutating one relates its old and new decoded stores by `Extend_store`. Stated
per function: `set_global`, `memory`, `memory_mut`, `grow_memory`, `set_table`,
`grow_table`, `define_*`, `export`, `func_type`.

**T7. No silent divergence.**
- **Statement:** if the interpreter loop runs `n` iterations without returning,
  then `c0` has a `StepsH` run of at least `n / K` steps, for a constant `K`.
  `K` bounds consecutive bytecode instructions that take no abstract step, such
  as slot copies and loop-head interrupt checks.
- **Consequence:** infinite interpretation implies infinite spec execution.

**Compiler completeness is not proved.** If `Accepts bytes profile m` holds and
`m` is within `CompileLimits`, then `compile` succeeds. The WAST corpus tests this behavior; it does not establish the theorem.


## Platform and callback contracts

| Id | Premise | Lean name | Responsible |
| --- | --- | --- | --- |
| A1 | Each `FloatOps` operation returns normally. For each operation , a non-NaN result decodes to an element of the spec result set; a NaN result occurs only when the spec result set contains a NaN. The proven Rust wrapper canonicalizes NaNs, which lands in the spec set. | `FloatOpsCorrect F` | Hardware, rustc, embedder (round-to-nearest-even, no FTZ, no fast-math) |
| A2 | For each current interpretation and valid store, `call_host` returns a store with the same indexed `Inv` under some new interpretation, agreement on all previously issued keys, and cross-interpretation `Extend_store`. It preserves raw store identity and existing function/type/instance prefixes, does not decrease the extern count, and returns `IssuedValue` values (same-store reference indices are in bounds; foreign references may be rejected). Result types are checked at runtime and are not assumed. | `HostWorldSound` plus `FrameStorePrefix`, extern monotonicity and result-issuance premises | Embedder. Checked returned API actions compose these store effects; callback normality and its decomposition into those actions remain explicit obligations. Nested proofs may use callback contracts established at smaller nesting depth. |
| A3 | Memory operations return normally. `bytes` returns the decoder view; `bytes_mut` provides a continuation writing back every same-length byte slice. Successful `new_zeroed` returns exactly the requested zero bytes. Successful `grow` preserves old bytes and appends zeros to the requested length; failed growth preserves the byte view. Creation and growth may fail. | Full `MemoryLaws M` | Embedder. Proven for extracted `VecMemory` under `AllocCorrect`. |
| A4 | Nothing outside a hook changes memory bytes, including interrupt-callback JS. | Folded into A2 and A3 | Embedder |
| A6 | Allocation returns normally and preserves vector contents and length; its Boolean answer is unrestricted. | `AllocCorrect A` | Internal allocator implementation |
| A7 | Host and interrupt callbacks return normally, without panic. | `HooksTotal P` | Embedder |
| A5 | Rust privacy holds: no `unsafe` code outside platform implementations reaches into `Store` or `Execution` internals. | Meta-level | Embedder, rustc |

`AllocCorrect A` requires `reserve` to return normally and preserve the
vector's modeled contents and length. Capacity is outside the extracted model.
`HooksTotal P` requires interrupt and host hooks to return normally; in
particular, Rust panics and foreign exceptions must not cross these boundaries.
Allocation success/failure and interrupt continue/terminate answers remain
unrestricted. These laws are explicit theorem premises, not extra axioms.

## Specification and native boundaries

`SpecExt.Builtins` defines all pinned builtin signatures. `SpecExt.Host` extends
the generated semantics with atomic host calls and omits post-call `Store_ok`.
That omission is an explicit weakening of the specification. `SpecExt.Wasm1`
states Wasm 1.0 segment-bounds failure and rollback. These handwritten target
semantics require review independently of proof checking.

The pinned `Step.vstore_lane_oob` compares lane width in bits against memory
length in bytes; the successful store rule uses the byte width. Consequently
both rules can apply to some stores. Actual byte-range failures imply the
source trap premise, so forward correspondence holds. No global determinism
or uniqueness claim follows from these proofs.

Native wrappers instantiate the generic functions. `StdAlloc` uses
`Vec::try_reserve`; native floating-point operations use Rust and `libm`.
Their compliance with platform laws is outside the kernel proof. Store
construction issues nonzero identities using checked atomic increments and
panics on identity exhaustion; it is outside the extracted no-panic guarantees
for compilation, invocation, and instantiation.

Host recording occurs at interpreter call boundaries, after argument decoding
and result checking. An invocation's trace records its direct host calls;
reentrant invocations have separate traces. Checked returned API actions can
compose callback effects, but establishing the callback's normal return and
its decomposition into those actions remains an embedder obligation.
