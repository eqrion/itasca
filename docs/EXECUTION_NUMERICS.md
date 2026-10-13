# Execution numerics and extraction boundary

The interpreter in [`src/runtime`](../src/runtime/mod.rs) is tested Rust, outside
Charon extraction and outside the validator's Lean guarantees. The entire runtime
module and its `libm` dependency are selected only under `cfg(not(charon))`.
No execution theorem, external axiom, or placeholder numeric model has been added
to the audited validator dependencies. See the [public trust boundary](../README.md#formal-verification).

## Representation and semantics

[`numeric.rs`](../src/runtime/numeric.rs) centralizes scalar numeric operations and
[`simd.rs`](../src/runtime/simd.rs) implements all 236 Core 2.0 SIMD opcodes using
portable integer lane operations. `Value::F32` and `Value::F64` contain raw IEEE
bits; `Value::V128` contains 128 bits, with lane zero in the least significant bits.
Loads and stores explicitly use little endian order and do not depend on the host's
byte order or vector instruction set.

Integer arithmetic wraps at its Wasm width. Shifts mask their counts. Signed
minimum divided by minus one traps, while signed remainder in that case is zero.
Division by zero has a separate trap. Trapping float-to-integer conversion checks
the truncated value against an exclusive upper bound, so negative fractions
between minus one and zero convert to unsigned zero. NaN conversion and numeric
overflow remain distinct traps. Saturating conversion uses Rust's specified
saturating float casts, including zero for NaN.

Native `f32`/`f64` operations implement ordinary IEEE arithmetic and conversions.
Pinned `libm = 0.2.16`, with default features disabled, supplies square root,
ceiling, floor, truncation, and absolute value under `no_std`. Nearest-integral
rounding implements ties-to-even and preserves negative zero explicitly. The
implementation relies on Rust's IEEE floating-point environment; embedding code
must not alter the hardware rounding mode or enable flushing of subnormals.
There are no fast-math operations or fused multiply-add substitutions.

Arithmetic NaNs are canonicalized at the numeric helper boundary. Sign-only
operations (`abs`, `neg`, `copysign`), constants, reinterpretation, and lane
movement preserve the required raw bits. Scalar/SIMD `min` and `max` handle
signed zero and propagate NaNs; SIMD `pmin`/`pmax` use the ordered comparison and
preserve the selected operand's bits, including a signaling NaN. Spec-permitted
NaN choices must be compared relationally in conformance tests. Final-output NaN
masking alone is insufficient for differential testing, since payloads can affect
control flow after reinterpretation.

Memory32 effective addresses add the unsigned address and offset in `u64`.
SIMD memory operations check the complete byte range before writing, preserve
unselected lanes, and trap instead of wrapping an overflowing address. Narrowing,
widening, pairwise addition, dot products, and Q15 rounded saturating multiply
use widened intermediates and explicitly truncate or clamp the result.

The semantic reference is the pinned [Core numeric definition](../vendor/spectec/document/core/exec/numerics.rst),
[SIMD opcode table](../vendor/spectec/proposals/simd/BinarySIMD.md), and the
[Core 2.0 SIMD corpus](../tests/spec2/simd). Unit regressions cover signed-zero
rounding, conversion boundaries, signed division/remainder, unsigned narrowing
from signed inputs, Q15 saturation, dot-product overflow, pseudo-min/max operand
selection, and memory address overflow/atomicity.

## Pinned extraction probes

The following probes were run against Charon `0.1.279`
(`c8f15d7d658c86a95658f71ad99cddd4be002e04`), the repository's pinned Aeneas
binary, and Rust `nightly-2026-09-17` before selecting the runtime extraction
boundary. Sources and generated artifacts were kept in a temporary directory,
outside the proof tree. Neither partially generated Lean files nor generated
external axioms were imported into the project.

| Probe Rust body / declaration | Charon | Aeneas Lean backend |
| --- | --- | --- |
| `(a & b) ^ (a >> (b % 32))`, with `u32` inputs | Success | Definitions emitted |
| `a.wrapping_add(b).rotate_left(b)`, with `u32` inputs | Success | Definitions using existing integer models emitted |
| `(a + b) * b`, with `f32` inputs | Success | Fails with `Invalid inputs for binop` |
| `a as i32`, with `f64` input | Success | Fails with `Unreachable` |
| `f32::from_bits(a).to_bits()`, with `u32` input | Success | Emission succeeds, but both functions become external axioms |
| `(a >> (n % 128)) & 255`, with `u128` and `u32` inputs | Success | Definitions emitted |
| `a.try_reserve(n).is_ok()`, with `&mut Vec<u8>` and `usize` inputs | Success | Emission succeeds, but reservation and its error type become external axioms |
| Value enum containing `u32`/`u128`, frame with `usize` PC/base, and `f.pc += 1` | Success | Types and state-update definition emitted |

An Aeneas exit status of zero is therefore **not** evidence that a primitive has
an audited executable model. Bit reinterpretation and fallible allocation need
concrete models and correctness arguments before crossing the proof boundary.
Native floating arithmetic and casts additionally need backend support or an
alternative modeled implementation. This decision does not block execution in
the independently tested Rust runtime.

The frame-loop optimization was also checked with a reduced probe of cached
frame indices, loop exits on calls/returns, and call-result reuse after charging.
That probe emitted Lean definitions and compiled without external axioms or
placeholders. Non-call instruction handlers and existing library dependencies
were represented by concrete stand-ins; it is not extraction of the interpreter.
Probing the full dispatch shape in both the original and optimized loops finds
the same pinned Aeneas borrow-join failure at the `br_table` index selection.
`Slice.last_mut` and `Vec.truncate` also require external models. Those gaps join
the numeric, allocation, and ownership work required for future runtime
extraction; no probe artifacts or new assumptions enter the validator audit.

The subsequent stack/dispatch/state-cache experiments also have pinned probes.
The exact new integer binary helpers and instruction-constructor mapping extract
and compile using the existing concrete `Vec.pop` model. A reduced probe retains
the new frame wrapper, cached PC/fuel loop, and local/constant dispatch, with
concrete stand-ins for other handlers and runtime dependencies. It compiles
using the same `Vec.pop` model and a scratch list-based model of the existing
`Slice.last` dependency. The checked helper declarations have no transitive
axioms beyond the standard Lean logical foundations. These are compatibility
checks, not runtime correspondence proofs; all probe files remain outside the
project's proof sources and audit imports.

The return/float/restart pass adds no new native numeric primitives. Its reduced
floating stack probe preserves the new operand-update and error-control paths,
using concrete integer stand-ins for the existing native floating helpers. The
new restart body also extracts with reduced concrete store, argument-checking,
and reservation dependencies. Both generated modules compile, and the checked
helper declarations depend only on the three standard logical axioms. Restart
uses `Vec.clear`, for which the probe supplies a concrete empty-vector model;
capacity and allocation failure remain outside that model. These probes check
control/borrowing compatibility, not floating semantics, the full runtime, or
restart correctness. They add no project imports, models, or assumptions.

The emitted bitwise, wrapping/rotation, `u128` lane, and frame-state modules were
also compiled successfully with `lake env lean` in the project's existing Lean
environment. This checks those small generated models; it is not a runtime
correctness proof.

A reproducible invocation for each standalone `probe.rs` is:

```sh
vendor/aeneas-lean/charon/charon/target/release/charon rustc \
  --preset=aeneas --sysroot=default \
  --exclude='{impl core::clone::Clone for _}' \
  --exclude='{impl core::marker::Copy for _}' \
  --dest-file="$TMPDIR/probe.llbc" -- --crate-type=lib "$TMPDIR/probe.rs"
vendor/aeneas-lean/src/_build/default/main.exe \
  -backend lean "$TMPDIR/probe.llbc" -dest "$TMPDIR" -no-progress-bar
```

Inspect generated declarations as well as exit status. Do not import output that
contains axioms. Any future verified runtime model must cover allocation/resource
outcomes, runtime invariants, instruction rewriting, callbacks, and observable
store effects as well as these numeric primitives.
