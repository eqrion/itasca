# Differential fuzzing

The validator targets compare itasca with pinned wasmparser. Run them from the
repository root with `cargo fuzz run TARGET`:

| Target | Contract |
| --- | --- |
| `raw_bytes` | Wasm 1.0 acceptance implies wasmparser acceptance. |
| `wasm1_smith` | Bounded generated Wasm 1.0 modules pass both validators. |
| `wasm2_raw_bytes` | Core 2.0 acceptance implies wasmparser acceptance. |
| `wasm2_smith` | Bounded generated Core 2.0 modules pass both validators. |

The Core 2.0 targets use `WasmFeatures::WASM2`; the generator enables all
Core 2.0 additions and disables later proposals. It exercises up to four tables
and at most one memory, limits signatures and functions, and varies unsigned
LEB encodings from one through five bytes. Before requiring acceptance it
independently checks the documented signature, local, body-byte, and module-byte
limits. It does not rewrite generated element or data sections.

The Core 2.0 targets select `ValidationProfile::Wasm2` and compare the complete
profile against wasmparser's Core 2.0 feature set. The generated-module target
keeps the validator's signature and module-size limits separate from language
features.

For example:

```sh
cargo fuzz run wasm2_raw_bytes -- -max_len=65536 -max_total_time=60
cargo fuzz run wasm2_smith -- -max_len=65536 -max_total_time=60
```

Raw-byte targets check soundness only because valid modules can exceed
implementation limits. Generated-module targets check completeness only within
those limits. Fuzzing complements the checked Lean theorems and the pinned
specification corpus; it does not replace them.

## Execution targets

The execution oracle is pinned **Wasmi 2.0.0**, with `std`, `validate`, `simd`,
and stable Rust enabled and optional text parsing disabled. Its
[proposal support](https://github.com/wasmi-labs/wasmi/tree/v2.0.0) covers Core 2.0,
including SIMD. The harness disables later proposals and uses its typed host
functions, tables, memories, globals, and resource controls. The separate
`runtime_wast` test runs itasca against both complete specification corpora;
Wasmi does not replace those conformance expectations.

| Target | Workload |
| --- | --- |
| `wasm1_execute` | Bounded Wasm 1 modules from wasm-smith, typed arguments, deterministic imports, and repeated calls to all exported functions. |
| `wasm2_execute` | The same, including Core 2.0 references, bulk operations, multiple tables, and SIMD. |
| `runtime_linking` | Shared imports, kind/type/limit mismatches, active segment failures, and start traps with prior memory effects. |
| `runtime_stateful` | Cross-instance calls, host traces, memory/table growth, bulk operations, segment drops, trapping writes, and subsequent observations. |
| `runtime_numeric` | Scalar and non-memory SIMD primitives, IEEE edge patterns, integer boundaries, and lane patterns. |
| `runtime_compile` | Arbitrary bytes through validation and rewriting; accepted bounded integer/reference programs also execute against Wasmi. |

The [shared comparator](../tests/support/runtime_differential.rs) compares typed
results, semantic trap classes, all exported/imported memories, tables and
globals, and ordered host calls with arguments. It checks effects after traps
and failed instantiation. Function identities receive matching symbolic IDs;
the pinned Wasmi version exposes no public function-handle equality, so its
store/function `Debug` identity is used only for lookup within that engine.
Private addresses are never compared between engines. Recheck this adapter
when updating the oracle. External references carry embedding-assigned symbols.

Generated programs export all objects and receive a source-level termination
guard with budget 100. They use at most one 16-page memory with a declared
maximum, four bounded tables, eight functions, and small type/index spaces.
Each itasca action permits five million interrupt checks at function entries
and loop headers. Itasca runs first; an interrupted action is excluded before
running Wasmi. Both engines run without fuel. Source instruction count,
call/operand limits, and action counts bound the workloads. Host functions log
their typed arguments and return zeros of their declared result types.

The generators canonicalize NaNs **after each floating-point operation**, before
reinterpretation, control flow, or stores can observe a payload. Focused numeric
cases use finite arithmetic inputs or operations whose bit behavior is
determinate for arbitrary inputs. Raw-byte execution excludes float/SIMD
instructions because it cannot insert that canonicalization; their compilation
is still exercised. Final NaN payloads are never simply ignored.

Historical Wasm 1 active-segment failures precheck every bound before writing.
Wasmi uses current sequential initialization even with Core 2 proposals disabled.
Such Wasm 1 instantiation failures are reported as `ProfileDifference`, with
their historical effects checked separately by the pinned Wasm 1 WAST corpus.
Mutable-global import/export support stays enabled in both oracle configurations
to match itasca's existing profile. Declared growth maxima and embedding caps
agree for generated workloads; unexpected interruption/stack/allocation exhaustion is a
separate `ResourceLimit`, never an equivalence success or a semantic mismatch.

Each target periodically reports counts for successful comparisons, invalid or
insufficient generator input, resource limits, historical profile differences,
unmapped references, and numeric nondeterminism exclusions. Inspect these rates
alongside libFuzzer coverage. The deterministic test
`cargo test --test runtime_differential` also freezes minimum useful generated
coverage and checks 4864 focused numeric/SIMD cases plus stateful/linking seeds.

For an instrumented campaign, install `cargo-fuzz` and run:

```sh
cargo fuzz run wasm1_execute -- -max_len=65536 -max_total_time=60
cargo fuzz run wasm2_execute -- -max_len=65536 -max_total_time=60
cargo fuzz run runtime_linking -- -max_len=128 -max_total_time=60
cargo fuzz run runtime_stateful -- -max_len=128 -max_total_time=60
cargo fuzz run runtime_numeric -- -max_len=64 -max_total_time=60
cargo fuzz run runtime_compile -- -max_len=65536 -max_total_time=60
```

`runtime_compile` interprets its first byte as the profile selector (even for
Wasm 1, odd for Wasm 2); seed it with that byte followed by actual Wasm modules.
The other target inputs are generator/action seeds. libFuzzer saves the original
input on failure; reproduce it using the same target and committed lockfile.
The target code fixes the generator configuration, import behavior, arguments,
actions, resource policy, and oracle version. Retain the failure output showing
both outcomes, minimize the seed, and promote confirmed engine bugs to a
deterministic regression.

The short instrumented baseline uses cargo-fuzz 0.13.1 and the pinned
`nightly-2026-09-17` toolchain, with AddressSanitizer and compiler coverage enabled.
The [campaign script](scripts/runtime_instrumented.py) seeds generated targets and
prefixes 100 valid binary fixtures with both profiles for `runtime_compile`.
It retains inputs, logs, and failure artifacts in the printed temporary directory:

```sh
cargo install cargo-fuzz --version 0.13.1 --locked --root /private/tmp/itasca-fuzz-tools
python3 fuzz/scripts/runtime_instrumented.py \
  --cargo-fuzz /private/tmp/itasca-fuzz-tools/bin/cargo-fuzz \
  --seconds 60
```

The slot runtime's agreed 60-second campaigns all passed on 2026-10-16:

| Target | Inputs | Comparisons | Invalid input | Resource exclusion | Profile exclusion | Numeric exclusion | Coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `wasm1_execute` | 597 | 399 | 196 | 0 | 2 | 0 | 41228 |
| `wasm2_execute` | 1487 | 804 | 683 | 0 | 0 | 0 | 39781 |
| `runtime_linking` | 1675 | 1675 | 0 | 0 | 0 | 0 | 22231 |
| `runtime_numeric` | 16199 | 16199 | 0 | 0 | 0 | 0 | 30465 |
| `runtime_stateful` | 572 | 572 | 0 | 0 | 0 | 0 | 27857 |
| `runtime_compile` | 33098 | 361 | 32538 | 3 | 0 | 196 | 25025 |

There were no unmapped-reference exclusions. These runs use the rewritten slot
runtime, synchronous hooks, and the no-fuel oracle configuration described above.
The compiler target's accepted floating/SIMD programs are compilation evidence;
its numeric exclusions are not counted as execution comparisons.

The following historical results predate the slot runtime rewrite. All four
initial 10-second instrumented campaigns completed without a failure:

| Target | Inputs | Semantic comparisons | Invalid input | Resource exclusion | Numeric exclusion | Final coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `wasm2_execute` | 322 | 112 | 210 | 0 | 0 | 39350 |
| `runtime_numeric` | 2604 | 2604 | 0 | 0 | 0 | 16759 |
| `runtime_stateful` | 133 | 133 | 0 | 0 | 0 | 27617 |
| `runtime_compile` | 6930 | 237 | 6574 | 1 | 118 | 23887 |

There were no historical-profile or unmapped-reference exclusions. Coverage is
libFuzzer's instrumented coverage count for each complete target, including the
harness and oracle; input counts vary with machine speed. These short campaigns
establish an instrumented baseline, not exhaustive execution coverage.

A separate bounded smoke check runs directly built libFuzzer binaries without
sanitizer or coverage instrumentation. Reproduce all six targets, deterministic
input seeds, fixed libFuzzer seeds, and reported exclusion rates with
`python3 fuzz/scripts/runtime_smoke.py`. Its raw-byte corpus prefixes 100 real
valid fixtures with each profile selector; logs and failure artifacts remain in
the printed temporary directory.
