# Differential fuzzing

The targets compare itasca with pinned wasmparser. Run them from the repository
root with `cargo fuzz run TARGET`:

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
