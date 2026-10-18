# Slot runtime benchmark comparison

Measured October 16, 2026 on aarch64 macOS (Darwin 24.5.0), using Rust 1.88.0
and the default release profile. The baseline is commit
`93d733ede4249c1af2804e09623ff3b817015d67`; the replacement is the working-tree
slot runtime after complete Aeneas translation and generated Lean compilation.
No compilation or extraction jobs ran during either measurement.

Each run uses nine samples targeting 50 ms per sample, alternating itasca and
Wasmi within each stage. The baseline run precedes the replacement run.
Workload outputs are checked outside the measured intervals. Raw samples and
per-stage min/median/max output are retained:

- [Baseline samples](execution-m1-before-arm64-macos.csv) and [output](execution-m1-before-arm64-macos.txt).
- [Slot-runtime samples](execution-m1-after-arm64-macos.csv) and [output](execution-m1-after-arm64-macos.txt).
- [Original historical baseline](runtime-arm64-macos.txt), retained unchanged.

The table compares `execute`: invocation and result handling on existing
instances, including fresh execution storage. Speedup is baseline / replacement;
values above one favor the replacement. These compare the requested APIs: the
old runtime meters fuel, while the new runtime uses interrupt callbacks. Its
Wasmi comparison also disables fuel. The new `compile_instance` stage includes
compilation because instances own their compiled module; it is not comparable
to the old `instantiate` stage. `restart` and `reuse` retain their respective
runtime's execution storage.

| Workload | Baseline µs | Slot runtime µs | Speedup |
| --- | ---: | ---: | ---: |
| `call_boundary` | 0.138 | 0.141 | 0.978× |
| `integer_loop` | 353.410 | 354.492 | 0.997× |
| `direct_calls` | 695.395 | 610.723 | 1.139× |
| `indirect_calls` | 782.348 | 695.878 | 1.124× |
| `float_loop` | 358.170 | 357.920 | 1.001× |
| `memory_sum_64k` | 907.965 | 846.594 | 1.072× |
| `bulk_copy_8m` | 134.949 | 135.432 | 0.996× |
| `simd_loop` | 535.235 | 410.624 | 1.303× |
| `many_functions` | 0.391 | 0.409 | 0.955× |
| `unary_conversion` | 749.830 | 642.084 | 1.168× |
| `memory_widths` | 1476.045 | 1291.350 | 1.143× |
| `recursive_calls` | 8.862 | 6.930 | 1.279× |
| `large_mixed_body` | 83.465 | 74.547 | 1.120× |
| `cross_instance` | 714.030 | 611.935 | 1.167× |

Call-heavy, SIMD, conversion, memory, and mixed-code workloads improve in
these measurements. Integer/float loops and bulk copy are near parity, and
`many_functions` execution is approximately 5% slower. Small differences near
parity are within the observed sample spread.

The logged frame-payload calculation currently multiplies logical value counts
by eight; it undercounts vector slots. Do not use that field as a v128 frame-size
measurement. Instruction-byte counts and the eight-byte scalar slot width are
independent of that reporting issue.

Reproduce each executable with:

```sh
runtime_bench --samples 9 --sample-ms 50 --csv results.csv
```

The source workload definitions and timing boundaries are in
[`examples/runtime_bench.rs`](../../examples/runtime_bench.rs).
