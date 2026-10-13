# Instantiation and execution

The `itasca::runtime` module compiles validated WebAssembly into immutable stack
bytecode, instantiates it in an append-only store, and executes it with resumable
fuel and host calls. Both existing language profiles are supported, including
all Core 2.0 SIMD operations. Execution is **not formally verified**. The existing
validator proofs and their premises remain unchanged.

```rust
use itasca::{runtime::*, ValidationProfile};
use std::rc::Rc;

let bytes = b"\x00asm\x01\x00\x00\x00";
let code = Rc::new(compile_with_limits(
    bytes, ValidationProfile::Wasm2, CompileLimits::default(),
)?);
let mut store = Store::new();
let mut initialization = store.instantiate(code, &[])?;
assert!(matches!(initialization.run(&mut store), Outcome::Returned(_)));
let instance = initialization.instance().unwrap();
# Ok::<(), Box<dyn std::error::Error>>(())
```

Use `compile_with_limits` for separate validation and compilation-resource
errors. The convenience `compile` uses default bounds and reports compiler
resource rejection as a visitor allocation error. Compilation occurs through
actual issued `CodeBatch` operations and operator callbacks. No executable is
published before the entire streaming driver accepts, including the tail and
outstanding workers. Artifacts are assembled by defined-function index rather
than worker completion order.

Bytecode branches contain destination PCs, activation-relative stack heights,
and ordered result/parameter counts. Structured labels and all immediates are
resolved before execution. Source maps report complete-module byte offsets;
function statistics separately record body bounds, local counts, and maximum
operand depth. The validator's polymorphic unreachable stack is never treated
as a concrete runtime layout.

## Stores and linking

An `ExecutableModule` can be shared by multiple instances. Supply `Extern`
imports in declaration order to `Store::instantiate`; names are available through
`ExecutableModule::env().imports()`. The store checks kind, structural function
type, table element type, global mutability/type, current size and declared
maximum, and store ownership. Imports refer to the provider's objects. Functions
always execute in their defining instance, including imported and indirect calls.
Function signatures are interned structurally within each store; indirect calls
compare store-local canonical IDs, including across separately compiled modules.

Function, table, memory, global, external-reference, and instance handles have
private store identity and index fields. Handles from another store are rejected.
Published objects are retained until the store is dropped. Provisional allocations
are discarded if initialization fails before publication and before any imported
object can be written. External references associate
an opaque `u64` identity with a store address; the embedding must keep the object
represented by that identity alive for the store's lifetime. Repeated calls to
`define_extern` create distinct identities even with the same embedding payload.

All function addresses are available before constant-expression evaluation.
Wasm 1.0 checks all active element/data bounds before any segment writes. Wasm
2.0 applies active segments sequentially, preserving earlier writes after a
later failure. Active and declarative elements are dropped as required, and
passive segment dropped state belongs to each instance. Dropped segments behave
as empty contents, including zero-length boundary checks.

A start trap does not roll back segment, host, or memory effects. Functions that
escape through imported tables before failure keep their defining instances
alive. An instantiation exposes its public instance handle only after successful
start completion. `Instantiation::run`, `add_fuel`, and `resume_host` continue
initialization without replaying allocation, segment writes, or host calls.

## Fuel, calls, and resource limits

Create `Execution::new(&store, function, arguments)`, add fuel, and call
`run(&mut store)`. An ordinary bytecode operation costs one unit. Calls add one
unit per initialized local (including parameters); initial invocation has the
same charge. Host calls instead add one unit per argument and two per expected
result to account for the request and continuation. Bulk memory/table instructions add one unit per 64 requested
bytes/elements, rounded up. Memory growth charges requested bytes using that
formula; table growth charges requested elements. All cost arithmetic is checked.

Insufficient fuel suspends before consuming operands, advancing the PC, or
mutating the store. Remaining fuel is retained. Atomic bulk work requires enough
accumulated fuel for its entire charge: repeatedly running with insufficient
fuel does not make progress. Every executable cycle consumes positive fuel.
Fuel counts are not a stable cross-version interface and do not bound elapsed
time, allocator latency, or embedding callback work.

A host call yields `NeedsHostCall` with its identifier, typed arguments, and
expected result types. Call `resume_host` on that same execution to provide its
result. Result arity, types, and reference ownership are checked. A second resume
is rejected. Type errors leave the request pending for correction. A separate
nested `Execution` permits reentrancy using the same store; the core retains no
mutable memory borrow across the host boundary. `run_with_host` supplies a
synchronous loop using the `Host` trait and preserves the execution if fuel runs
out. Host deadlines and cancellation remain embedding responsibilities.

Default store limits are 1,000,000 runtime objects (including interned signatures), 10,000 retained instances,
1,000,000 instance metadata/initial-element items, 256 MiB total linear memory,
1,000,000 parameter/result entries in canonical signatures,
1,000,000 live table elements, 1,024 frames per execution, and 1,000,000 live
local/operand values per execution. `StoreLimits` can change these bounds.
Compiler limits independently constrain input bytes and generated artifacts
before invocation. Initial allocation failure and resource limits are explicit
errors. Failed Wasm memory/table growth returns its Wasm failure value and leaves
existing state intact. Host memory allocation is fallible where the runtime
allocates; the existing validator still has its documented successful-allocation
premise. Store identity exhaustion panics rather than reusing an identity.
Aggregate memory/table use is maintained at successful allocation and growth,
so a charged growth operation does not scan every object in the store.

## Evidence and remaining proof work

The [WAST harness](../tests/support/runtime_wast.rs) executes the pinned corpora
with persistent script state, typed imports, exact integer/float bits, allowed
NaN patterns, vector lanes, and reference identities. It checks effects after
traps and failed initialization. Both profiles have frozen directive totals and
zero unsupported cases. Fuel timeout and unexpected resource exhaustion are
failures, never substitutes for a requested Wasm trap. Existing validation
corpus gates remain in place.

The [API regressions](../tests/runtime_api.rs) cover cross-instance resolution,
store ownership, host reentrancy and result checking, retained fuel, atomic bulk
operations, segment drops, start continuation, escaping functions, failure effects,
and explicit call-stack limits. The [numeric boundary](EXECUTION_NUMERICS.md)
records tested semantics and actual pinned extraction results.

The runtime is excluded with `cfg(not(charon))`. Its native numeric operations,
fallible allocations, reference ownership, and interpreter implementation are not
part of the extracted validator model. New execution contracts do not add axioms
or weaken the validator audit. Compiler correctness, concrete runtime invariant
preservation, and full simulation against usable SpecTec execution rules remain
separate proof obligations. Do
not infer execution correctness from accepted module typing or a passing corpus.

The checked [Core 2.0 callback correspondence](../lean/Itasca/MultiValue/CallbackCorrespondence.lean)
extends the existing Wasm 1.0 body trace guarantees. It relates actual callback
names, order, and immediates to independent byte encodings, aligns accepted
traces with generated typing, and preserves ordinary outcomes under
instrumentation. Rejected callbacks and partial branch-table vectors are
retained. These are validator callback theorems; they do not establish that
the new rewriting compiler consumes those callbacks correctly.

Run `cargo test` and `cargo test --no-default-features` for both validation and
execution gates. The ordinary extraction and Lean checks remain required.
`ITASCA_WAST_FILE` filters execution scripts during diagnosis; unfiltered runs
check the frozen complete totals. See [fuzzing](../fuzz/README.md) for independent
execution comparisons and their resource/nondeterminism exclusions.

Bytecode well-formedness, branch and stack preservation, store/frame invariants,
host-continuation consumption, and bounded-fuel proofs are deferred. Independent
runtime invariant models are not retained. The concrete Core 2.0 callback
proofs above remain part of the validator audit.

## Performance baseline

Run the nine-workload comparison with the pinned Wasmi 2.0.0 interpreter:

```sh
cargo run --release --example runtime_bench -- --csv /tmp/itasca-runtime.csv
```

`--samples N`, `--sample-ms N`, and `--filter NAME` select sample count, target
batch duration, and workload substring. Defaults are nine samples and a 50 ms
calibration target, capped at one million iterations per batch. The runner
alternates engine order between samples and prints the median, minimum, and
maximum batch-average time per operation. WAT parsing/encoding and known-result
comparisons occur outside the clocks. Results are checked before and after
sampling; each invocation must return successfully. CSV includes every sample's
iteration count, elapsed nanoseconds, and time per operation.

Both engines use fuel metering. Wasmi compiles eagerly, and both use the case's
Wasm 1.0 or Core 2.0 feature profile. Their fuel units are different and are never
compared. The three measurements have explicit lifetimes:

- **Compile:** complete-module validation and translation, including destruction.
  Wasmi engine setup and destruction are included on every iteration because its
  engine retains compiled function storage after a module is dropped. This is
  a fresh-engine compilation lifecycle measurement in a warmed process.
- **Instantiate:** a fresh store, instantiation from already compiled code,
  exported-function lookup, and cleanup. Engine/module creation is excluded.
  None of these fixtures has a start function.
- **Execute:** dynamic invocation, argument/result handling, fuel provisioning,
  and cleanup on a reused instance. This includes itasca's new `Execution`
  allocation and Wasmi's use of pooled execution storage. Export lookup and
  compilation are excluded; fuel-count reporting is outside the timing.

The recorded run used Rust 1.88.0 (LLVM 20.1.5), `aarch64-apple-darwin`, Darwin
24.5.0, the default Cargo release profile, and no `RUSTFLAGS` or release-profile
environment overrides. No builds or test campaigns ran concurrently. These
are local microbenchmarks with a hot working set, not application throughput
estimates. Full timing ranges and footprints are in the [run output](benchmarks/runtime-arm64-macos.txt);
all 486 measured samples are in the [CSV](benchmarks/runtime-arm64-macos.csv).

Execution medians per exported invocation:

| Workload | itasca µs | Wasmi µs | itasca / Wasmi |
| --- | ---: | ---: | ---: |
| `call_boundary` | 0.142 | 0.051 | 2.78× |
| `integer_loop` | 638.718 | 28.693 | 22.26× |
| `direct_calls` | 1161.326 | 83.062 | 13.98× |
| `indirect_calls` | 1301.182 | 138.561 | 9.39× |
| `float_loop` | 681.767 | 34.711 | 19.64× |
| `memory_sum_64k` | 1650.376 | 72.557 | 22.75× |
| `bulk_copy_8m` | 138.261 | 136.163 | 1.02× |
| `simd_loop` | 786.409 | 41.778 | 18.82× |
| `many_functions` | 0.731 | 0.067 | 10.87× |

The numeric and call loops each run 10,000 iterations. `call_boundary` is one
identity call. `memory_sum_64k` loads and sums 16,384 words from a 64 KiB active
data segment. `bulk_copy_8m` first fills 64 KiB, then copies that same hot region
128 times into a second 64 KiB region; it does not traverse an 8 MiB working set.
`simd_loop` accumulates four integer lanes. `many_functions` compiles 128 helpers
plus an exported wrapper, but each invocation calls only the final helper, which
contains 32 additions. These instruction patterns allow each engine's own
translation optimizations.

Compilation and instantiation medians per module:

| Workload | Compile itasca µs | Compile Wasmi µs | Instantiate itasca µs | Instantiate Wasmi µs |
| --- | ---: | ---: | ---: | ---: |
| `call_boundary` | 1.452 | 4.313 | 0.356 | 0.441 |
| `integer_loop` | 1.913 | 5.059 | 0.356 | 0.443 |
| `direct_calls` | 2.527 | 5.663 | 0.355 | 0.450 |
| `indirect_calls` | 2.733 | 6.489 | 0.638 | 0.766 |
| `float_loop` | 1.923 | 5.027 | 0.352 | 0.440 |
| `memory_sum_64k` | 35.490 | 6.911 | 2.427 | 2.425 |
| `bulk_copy_8m` | 1.975 | 5.365 | 1.702 | 1.803 |
| `simd_loop` | 1.947 | 5.081 | 0.357 | 0.439 |
| `many_functions` | 258.537 | 270.804 | 1.003 | 1.705 |

The main execution gap is in the instruction-heavy loops; bulk copying is close
between the engines. Small code-heavy modules compile faster with itasca under
the measured lifecycle, while the data-heavy module compiles substantially more
slowly. Profiling is needed to attribute either gap to particular implementation
costs; these timings alone do not identify the cause.

The runner also reports live instruction and branch-table bytes, source bytes,
and the largest per-function local/operand payload bound. Instructions and values
are each 32 bytes on this target. The many-function fixture has 8,451 instructions
occupying 270,432 bytes. Payload bounds exclude vector spare capacity, call-frame
and source metadata, module declarations, linear memories, tables, allocator
bookkeeping, and engine storage; they are not heap/RSS measurements.

Native SIMD, packed bytecode, and superinstructions are not enabled in itasca.
Future changes should preserve trap/host-effect order and fuel semantics and be
measured against this baseline. Runtime proof work remains deferred.
