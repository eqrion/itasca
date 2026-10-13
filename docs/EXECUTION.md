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

After completion or a terminating execution error, `Execution::restart` accepts
another function and argument slice from the same store. It reuses frame and
local capacity, resets fuel to zero, and clears previous failure/source state.
Active, suspended, and host-pending executions reject restart. Argument/type,
store-ownership, and resource checks precede reset; a rejected restart preserves
the completed execution for inspection. Returned vectors remain owned by the
caller, so restarting does not recycle their allocation. Separate `Execution`
values still provide independent storage for nested calls.

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

The checked [Core 2.0 callback correspondence](../lean/Itasca/Wasm2/Trace/Correspondence.lean)
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

Run the fourteen-workload comparison with the pinned Wasmi 2.0.0 interpreter:

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
compared. The measurements have explicit lifetimes:

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
- **Restart:** the same dynamic invocation with an explicit `Execution::restart`
  on a completed execution. Frame/local buffers are warmed before timing and
  retained between calls; returned operand vectors still have their usual owned
  lifetime. Wasmi uses the same pooled call path as in execute. No start function
  or host callback is present in these fixtures.

The original nine-workload run below used Rust 1.88.0 (LLVM 20.1.5), `aarch64-apple-darwin`, Darwin
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

### Frame-loop optimization

The interpreter now retains the active frame's index and code identity in an
inner loop. Every call and return exits that loop before the next instruction,
and initial invocation is handled once per run. Call target resolution supplies
both the fuel charge and the executed target. An insufficient budget discards
the lookup, including errors, so resumption observes current table contents.
Scalar dispatch is inlined, fixed-cost instructions return their one-unit cost
directly, and branches/returns skip empty or identity stack copies.

These changes preserve bytecode, fuel charges, source offsets, and effect order.
The future proof obligations are local: the active frame remains fixed between
calls/returns, no store mutation separates lookup from invocation, and empty or
identity copies preserve the stack. Inlining does not change Rust semantics.
The [extraction boundary](EXECUTION_NUMERICS.md) still applies.

A fresh comparison used the same machine, toolchain, release settings, runner,
and nine-sample/50 ms protocol as above. The optimized executable ran immediately
before a saved baseline executable, with no builds or tests competing for CPU.
Execution medians in microseconds per invocation were:

| Workload | Before | After | Time reduction |
| --- | ---: | ---: | ---: |
| `call_boundary` | 0.141 | 0.140 | 0.6% |
| `integer_loop` | 641.439 | 499.476 | 22.1% |
| `direct_calls` | 1176.810 | 921.418 | 21.7% |
| `indirect_calls` | 1306.904 | 1011.911 | 22.6% |
| `float_loop` | 688.153 | 503.970 | 26.8% |
| `memory_sum_64k` | 1659.853 | 1311.877 | 21.0% |
| `bulk_copy_8m` | 142.571 | 141.068 | 1.1% |
| `simd_loop` | 790.383 | 649.752 | 17.8% |
| `many_functions` | 0.729 | 0.583 | 20.1% |

The instruction-heavy cases improve by 18–27%; the small differences in call
boundary and bulk-copy time are within measurement variation. Bytecode footprints
and fuel counts match exactly in all nine workloads. The [raw output](benchmarks/runtime-optimization-arm64-macos.txt)
records ranges, compilation, instantiation, and Wasmi measurements; the
[CSV](benchmarks/runtime-optimization-arm64-macos.csv) contains all 972 samples,
with a `version` column distinguishing the runs. These remain hot-working-set
microbenchmarks, not application throughput estimates.

### Stack, dispatch, and frame-state experiments

Three further changes were measured independently against the frame-loop version
above, then combined:

1. **Stack:** nontrapping integer binary arithmetic and comparisons pop the right
   operand and replace the left in place. This removes the second pop and the
   result push, including its capacity check. Underflow and type errors retain
   their original operand-consumption behavior; trapping arithmetic is unchanged.
2. **Dispatch:** locals, scalar constants, and scalar numeric instructions have
   dedicated bytecode variants. The compiler emits one instruction per callback
   as before, and these variants directly reach their handlers with a fixed
   one-unit charge. Generic instructions keep their existing cost calculation.
3. **Cached state:** the inner loop uses a local PC, fuel counter, and local base.
   Its wrapper publishes PC and fuel on every ordinary exit, including runtime
   errors. Calls and returns execute after publication. Branches return their
   target PC, and loop handlers neither change the frame stack nor read the
   temporarily stale frame PC or execution fuel.

All three are retained. Each keeps the same per-instruction suspension boundary
and source position; no instruction fusion or batched charging is involved.
Their future correspondence arguments are a stack-update equality, a direct
instruction-constructor mapping, and a relation between the cached and stored
PC/fuel. The [extraction probes](EXECUTION_NUMERICS.md) check the new code patterns
without changing the runtime's unverified status.

The following execution medians are microseconds per invocation. Each variant
used nine samples and a 50 ms calibration target, on the same toolchain and
machine as above. All five executables were built first, and the runs occurred
sequentially without concurrent builds or tests. The baseline here already
includes the preceding optimization pass.

| Workload | Baseline | Stack only | Dispatch only | Cached state only | All three | Combined time reduction |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `call_boundary` | 0.141 | 0.139 | 0.141 | 0.138 | 0.138 | 2.0% |
| `integer_loop` | 497.898 | 457.193 | 455.743 | 457.795 | 361.241 | 27.4% |
| `direct_calls` | 926.223 | 853.567 | 864.357 | 883.221 | 729.894 | 21.2% |
| `indirect_calls` | 1026.950 | 960.505 | 967.671 | 981.859 | 814.130 | 20.7% |
| `float_loop` | 514.906 | 492.834 | 439.505 | 480.859 | 371.020 | 27.9% |
| `memory_sum_64k` | 1324.474 | 1190.685 | 1187.178 | 1210.782 | 912.690 | 31.1% |
| `bulk_copy_8m` | 137.240 | 138.815 | 138.484 | 142.242 | 139.370 | -1.6% |
| `simd_loop` | 648.474 | 662.226 | 619.983 | 634.620 | 538.759 | 16.9% |
| `many_functions` | 0.586 | 0.529 | 0.517 | 0.570 | 0.387 | 33.9% |

The combination reduces instruction-heavy execution time by 17–34% beyond the
previous pass. The isolated stack change slightly regresses the SIMD fixture,
but the combination improves it. Small call-boundary and bulk-copy differences
remain within measurement variation. All variants preserve fuel counts,
instruction counts, and bytecode footprints; instructions remain 32 bytes on
this target. [Raw output](benchmarks/runtime-experiments-arm64-macos.txt) records
ranges and the compilation/instantiation measurements, and the
[CSV](benchmarks/runtime-experiments-arm64-macos.csv) contains all 2,430 samples.

### Return, numeric, memory, and invocation experiments

The next pass tested four candidates independently, then narrowed the combination:

- **Cached result arity:** a frame records its result count when the call starts.
  Return no longer follows its function address through the function and type
  tables. The frame shrinks from 56 to 48 bytes on this target. The invariant is
  equality with the target's immutable signature; call setup already reads it.
- **More in-place scalar updates:** floating binary arithmetic and comparisons
  now replace the left operand after popping the right, using the same numeric
  helpers and preserving error consumption. An additional unary/conversion
  rewrite was rejected: its five-sample pilot slowed `unary_conversion` from
  768 to 834 µs. Keeping only the floating binary change improved that pilot's
  follow-up float loop without the conversion regression.
- **Fixed-width memory helpers:** explicit 1/2/4/8-byte paths were tested with
  complete bounds checks before writes and unchanged little-endian semantics.
  They are not retained. The first form regressed even non-memory loops;
  outlining `memory_op` removed that broad slowdown, but the memory-width case
  still took 1575 µs against 1502 µs for the baseline. Outlining the original
  byte loop took 1607 µs. These results show sensitivity to generated code as
  well as the byte-access implementation; unrolling alone was not a useful win.
- **Invocation reuse:** `Execution::restart` retains local and frame allocations
  explicitly. It only resets a finished execution, after validating the new
  function/arguments and reserving space. Its future invariant is equivalence
  to `Execution::new` apart from vector capacity. It introduces no shared pool
  or changes to host-continuation ownership. Returning still transfers the
  operand vector, whose allocation is not retained by restart.

The runner now includes five more workloads. `unary_conversion` performs integer
bit counting and float conversions/rounding in a 10,000-iteration loop.
`memory_widths` stores and loads 1/2/4/8-byte values at unaligned addresses.
`recursive_calls` descends 128 calls. `large_mixed_body` has 1,024 repeated groups
of integer, float, conversion, and memory operations: 19,458 bytecode instructions
occupy 622,656 bytes. `cross_instance` repeats calls into another instance whose
helper reads its defining global. Its compile timing and reported footprint cover
only the consumer; instantiation includes the already-compiled provider. Both
engines check known results before/after sampling, and all variants retain
identical instruction counts, payload bounds, and itasca fuel charges.

The retained combination is result-arity caching, floating binary stack updates,
and the optional restart API. The larger mixed body and deeper call tests broaden
the evidence, but these are still microbenchmarks, not application throughput.

Full comparisons used nine samples and a 50 ms target, with saved executables run
sequentially (combined, float-only, returns-only, restart-only, baseline) and no
concurrent builds or tests. The baseline already includes the preceding two
passes. The following medians are microseconds per invocation. “Restart only”
uses the old instruction handlers with the new reuse API; “Combined fresh” uses
`Execution::new`, and “Combined restart” uses `Execution::restart`.

| Workload | Baseline | Returns only | Float only | Restart only | Combined fresh | Combined restart |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `call_boundary` | 0.139 | 0.134 | 0.136 | 0.053 | 0.139 | 0.052 |
| `integer_loop` | 354.751 | 356.712 | 355.310 | 356.005 | 358.359 | 356.185 |
| `direct_calls` | 718.511 | 699.166 | 718.758 | 714.541 | 693.331 | 688.372 |
| `indirect_calls` | 800.548 | 785.349 | 803.230 | 793.895 | 775.997 | 774.668 |
| `float_loop` | 366.085 | 365.170 | 350.665 | 364.590 | 359.001 | 351.601 |
| `memory_sum_64k` | 897.148 | 894.553 | 895.170 | 899.120 | 909.473 | 899.195 |
| `bulk_copy_8m` | 136.984 | 135.153 | 135.730 | 135.440 | 146.595 | 135.837 |
| `simd_loop` | 533.577 | 530.896 | 533.306 | 532.835 | 534.303 | 534.254 |
| `many_functions` | 0.388 | 0.379 | 0.387 | 0.302 | 0.390 | 0.294 |
| `unary_conversion` | 751.388 | 756.045 | 742.396 | 745.117 | 743.864 | 737.288 |
| `memory_widths` | 1484.294 | 1515.036 | 1466.793 | 1455.011 | 1462.141 | 1458.007 |
| `recursive_calls` | 9.020 | 8.850 | 9.015 | 7.718 | 8.840 | 7.548 |
| `large_mixed_body` | 87.829 | 90.968 | 83.432 | 86.035 | 83.169 | 82.720 |
| `cross_instance` | 743.382 | 713.420 | 736.397 | 731.346 | 714.109 | 707.984 |

The isolated return change improves direct/indirect calls by about 2–3% and
cross-instance calls by 4%. Floating binary updates improve the float loop by 4%
and the large mixed body by 5%. Combined fresh invocations improve call-heavy
cases by 2–4% and the mixed body by 5%; other instruction-heavy cases are mostly
within 1–2%. Explicit restart reduces the tiny identity-call time by 63%, the
short many-function invocation by 24%, and the recursive invocation by 16%
relative to the baseline's fresh executions. These reuse gains include avoided
frame/local allocation and destruction, not just interpreter dispatch.

The full run's fresh bulk-copy measurement is 7% slower, with wide timing ranges
and simultaneous variation in the Wasmi control. Its restart measurement is
unchanged. Two focused repeat pairs, in opposite run orders after verification
finished, measured fresh baseline/combined times of 136.013/136.313 µs and
135.450/136.094 µs: within 0.5%. The 7% difference did not reproduce.

[Raw output](benchmarks/runtime-followup-arm64-macos.txt) includes all variants,
measurement order, source hashes, and timing ranges. The
[CSV](benchmarks/runtime-followup-arm64-macos.csv) preserves the pilot, follow-up,
full-run, and focused bulk-copy samples (9,576 total), with separate round/variant columns.
