# Verified execution plan

This document plans the replacement of the unverified runtime in `src/runtime/`
with an interpreter whose behavior is proven against the SpecTec-generated
Wasm 2.0 reduction semantics (`Step`). It records the decisions made so far, the
theorems and premises, the Rust redesign, the Lean proof architecture and file
layout, and an ordered sequence of milestones with tasks.

Tasks are tagged by the kind of work they need:

- **[B]** boilerplate: mechanical, well-specified, and checkable by tests or by
  Lean elaboration. Suitable for delegation.
- **[D]** design or proof engineering that needs judgment. Do these first in each
  milestone, so the [B] work has a fixed shape to fill in.
- **[R]** review of a trusted artifact against the official specification prose.

## 1. Decisions

| Topic | Decision |
| --- | --- |
| Target | Wasm 2.0 and Wasm 1.0. Wasm 1.0 differs at runtime only in instantiation (bounds pre-check), so it adds little. |
| Existing runtime | Replaced outright. No compatibility shims. |
| Floating point | Native `f32`/`f64` behind a trait. Its IEEE behavior is a theorem premise. A verified softfloat instance is optional future work. |
| Host calls | Synchronous hook called with the interpreter frame on the native stack. No suspend/resume. |
| Interrupts | Synchronous hook polled at loop headers and function entry. It returns continue or terminate and receives no store access. SpiderMonkey guarantees interrupt JS never touches the store. |
| Fuel | Removed from the API. Deterministic tests use a counting interrupt implementation. |
| Linear memory | Embedder-provided buffer behind a trait, bounds-checked as a Rust slice. A proven `Vec<u8>` implementation is the default. Signal handling and guard pages are out of scope. |
| Reentrancy depth | SpiderMonkey's native stack checks. A hook reports overflow as an error. |
| Spec additions | Live in `lean/SpecExt/`, separate from generated files, so every handwritten addition is visible in one place. |
| Validator | Its proofs, theorem statements, and extracted model stay unchanged. Dependencies point one way: execution proofs may import validator proofs, never the reverse. |

## 2. Background: what the generated specification provides

`lean/SpecTec/wasm2.0.lean` defines `Step`, `Steps`, `fun_instantiate`,
`fun_invoke`, store extension (`Extend_store`), and store validity
(`Store_ok`). Several gaps shape this plan:

1. **Opaque builtins.** 64 SpecTec definitions marked `hint(builtin)` are
   emitted as `opaque ... := Inhabited.default`. Nothing can be proven about
   them. They cover:
   - all float operations;
   - most integer operations (`iand_`, `ior_`, `ixor_`, shifts, rotates,
     `iclz_`, `ictz_`, `ipopcnt_`, `extend__`, `wrap__`);
   - `truncz`, which `idiv_` and `irem_` use;
   - byte encodings (`nbytes_`, `inv_nbytes_`, and relatives), which every load
     and store uses;
   - lane views (`lanes_`, `inv_lanes_`), which every SIMD rule uses.

   SpecTec 3.0 marks the same operations builtin, so this is by design.
2. **No host functions.** `funcinst.CODE : func`. SpecTec 3.0 adds
   `funccode = func | hostfunc` but no reduction rule for it.
3. **`sorry` theorems.** `Step_is_wf` and two siblings are `theorem ... := sorry`.
   The audit already rejects any dependency on them. Never use them.
4. **Well-formedness premises.** Every `Step` rule has `wf_config` premises on
   both sides. We need a lemma library that builds `wf_config` from component
   facts (section 7.4, `Exec/Spec/Wf.lean`).

## 3. Guarantees

### 3.1 Kind of guarantee

The main theorems are **soundness**: whenever the interpreter gives an answer,
some spec execution produces that answer. The spec is nondeterministic only at
NaN bit patterns, at `memory.grow`/`table.grow` failure, and at host calls.
Elsewhere, a returned answer is the unique spec answer.

Soundness alone permits an interpreter that always gives up. Theorems T4, T5,
and T7 therefore constrain the escape hatches (exhaustion, termination,
rejection, divergence) to stated causes.

### 3.2 Definitions used by the theorems

| Name | Meaning |
| --- | --- |
| `decodeStore : Exec.store.Store M → store` | Reads the extracted Rust store as a spec store. Addresses are store indices on both sides, so address decoding is the identity. |
| `decodeVal`, `decodeVals` | Typed decoding of public `Value`s. |
| `Inv st` | The store invariant (section 7.9). It implies `wf_store (decodeStore st)`. |
| `StepH`, `StepsH` | Generated `Step` plus labeled host-call rules (section 7.3). Labels record host events. |
| `Accepts bytes profile m` | Existing validator guarantee: `bytes` encodes `m` under the independent grammar, `Module_ok m`, and `m` satisfies the profile. |
| `P` | Platform instance: `Platform`, `FloatOps`, `MemoryBuffer`, and the internal `Alloc` (section 6.2). |
| `Recording P` | Proof-only wrapper of `P` that logs every host call. This follows the pattern in `Itasca/Visitor/Recording.lean`. |

### 3.3 Top-level theorems

All theorems are stated over the extracted generic functions. The public
monomorphic wrappers (section 6.2) are one-line instantiations with the native
platform and are reviewed rather than extracted.

**T1. Compilation.** If `compile(bytes, profile, limits) = Ok(exe)`, then:
- `Accepts bytes profile m` for some `m`;
- `CodeRel m exe` (section 7.6) holds.

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
- **`Err(Link _)`:** the store is unchanged.

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
  log recorded by `Recording P`. The log covers function address, arguments,
  and results or trap.

The theorem holds for every `P` satisfying the premises in section 3.4. In
particular, it holds for every answer the interrupt and allocation methods could
give.

**T4. Safety and bounded escape hatches.**
- The extracted `invoke`, `instantiate`, and `compile` never panic. That rules
  out overflow, out-of-bounds indexing, and failed unwraps.
- `Exhausted` is returned only when one of the following holds:
  - `Alloc::reserve` returned false for a request bounded by the spec state's
    needs (for example, the callee's slot count);
  - the decoded config's `FRAME_` nesting depth reached `StoreLimits` frame
    depth;
  - a host hook returned `HostError::StackOverflow`.
- `Terminated` is returned only after `Platform::interrupt` returned `Terminate`.

Every bound is stated over decoded spec quantities, never internal counters.

**T5. Rejection completeness at the API.**
- `invoke` never returns `BadArguments` for arguments that are well-typed
  against `f`'s type in `decodeStore st`.
- `instantiate` never returns `Link` when the imports satisfy the spec's
  `Externaddr_ok` typing.
- `memory.grow`/`table.grow` return failure only if one of these holds:
  - `MemoryBuffer::grow` or `Alloc::reserve` returned false;
  - the declared maximum would be exceeded;
  - a `StoreLimits` bound would be exceeded.

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

**Deferred: compile completeness (T8).** If `Accepts bytes profile m` holds and
`m` is within `CompileLimits`, then `compile` succeeds. This builds on the
validator's completeness proof. Until it is proven, the WAST corpus covers it.

### 3.4 Premises

| Id | Premise | Lean name | Responsible |
| --- | --- | --- | --- |
| A1 | For each `FloatOps` operation (listed in section 6.4): a non-NaN result decodes to an element of the spec result set; a NaN result occurs only when the spec result set contains a NaN. The proven Rust wrapper canonicalizes NaNs, which lands in the spec set. | `FloatOpsCorrect F` | Hardware, rustc, embedder (round-to-nearest-even, no FTZ, no fast-math) |
| A2 | `call_host` returns a store satisfying `Inv` that extends the old store (`Extend_store`). Result types are checked at runtime and are not assumed. | `HostSound P` | Embedder. Justified when the hook uses only the public API and nested `invoke` (by T3/T6 and induction on nesting depth), plus direct ArrayBuffer writes during the hook. |
| A3 | Embedder `MemoryBuffer` laws: `bytes` reads back what `bytes_mut` wrote, and length is unchanged by that path. Successful `grow` appends zeros. Failed `grow` changes nothing. | `MemoryLaws M` | Embedder. Proven for `VecMemory`. |
| A4 | Nothing outside a hook changes memory bytes, including interrupt-callback JS. | Folded into A2 and A3 | SpiderMonkey |
| A5 | Rust privacy holds: no `unsafe` code outside platform implementations reaches into `Store` or `Execution` internals. | Meta-level | Embedder, rustc |

No premise is needed for `Platform::interrupt` or `Alloc::reserve`. The theorems
quantify over all of their answers.

### 3.5 Trusted base

- SpecTec-generated `Step`, `fun_instantiate`, `fun_invoke`, `Extend_store`
  (generated from pinned sources plus versioned patches).
- `lean/SpecExt/`: builtin definitions, the host rule and the `funccode`
  backport, and the Wasm 1.0 instantiation statement. Each is transcribed from
  the official prose and needs [R] review.
- Existing items: the binary grammar, Charon/Aeneas translation and standard
  library models, rustc, and Lean's kernel.
- Public monomorphic wrappers in `src/runtime/native.rs` (section 6.2).

### 3.6 Known weakenings

- **`Store_ok` omitted from the host rule.** The prose additionally requires
  `Store_ok s'` after a host call. Proving it requires store typing, which is
  part of Wasm type soundness. The host rule omits it at first. This makes the
  spec more permissive only at host calls.
- **No completeness for `compile`** until T8.
- **NaN payloads:** any payload the spec permits is accepted. Deterministic
  payloads would need a stronger A1.

## 4. Specification extension mechanism

### 4.1 Splitting the generated file

The builtin signatures refer to types defined in the generated file itself, so a
handwritten module cannot be imported by `wasm2.0.lean` directly. Generation
therefore gains a deterministic split stage, `lean/scripts/spec_split.py`, run by
`make spec-generate` after SpecTec:

1. **Input:** the raw SpecTec output `.build/wasm2.0.raw.lean`.
2. **Split point:** the first `opaque` builtin declaration. The script fails if
   any builtin's signature mentions a declaration defined after that point.
3. **Outputs:**
   - **`SpecTec/Wasm2Prefix.lean`:** generated declarations before the split
     point.
   - **`SpecTec/wasm2.0.lean`:** the remainder. It starts with
     `import Wasm2Prefix` and `import SpecExt.Builtins`, and has every
     `opaque <builtin> ... := by first | ...` block removed.
   - **`SpecTec/Wasm2Builtins.lean`:** one
     `example : <generated signature> := @<name>` per removed builtin. It
     imports `Wasm2Prefix` and `SpecExt.Builtins`. This file pins every
     handwritten definition to the exact generated signature.
4. **Failure conditions:**
   - an `opaque` declaration remains that the script cannot match;
   - a builtin block has an unexpected shape;
   - the set of removed names differs between runs.
5. **Spec checks:** `spec-compare` and `spec-check` compare all three generated
   files.

The validator keeps `import «wasm2.0»`. Its proofs rebuild once and must pass
unchanged. AGENTS.md is updated to describe the split stage as part of the
generator.

### 4.2 Builtin definitions

`lean/SpecExt/Builtins/` defines each builtin with its exact generated name, in
the root namespace (the generated file refers to them unqualified). These files
may import only `Wasm2Prefix` and Lean/Batteries/Mathlib.

Before real definitions exist, a builtin may be a handwritten `opaque` with the
generated signature. That keeps the split behavior-preserving. Replace them
family by family (section 8).

### 4.3 Host functions

`patches/spectec-wasm2-hostfunc.patch` backports SpecTec 3.0's
`syntax funccode = func | hostfunc`. Here `hostfunc` carries a natural-number
host identity, so the patch defines it as `HOST nat`. It updates `funcinst.CODE`
and the 2.0 rules that read `CODE`. Check its effect on the validator with
`just prove`. Validator proofs are expected not to inspect `funcinst.CODE`.

`SpecExt/Host.lean` defines `StepH` on top of the generated `Step` (section 7.3).

## 5. Extraction layout

The validator's extracted model `lean/Itasca/Generated/{Types,Funs}.lean` must
stay byte-identical. The runtime is extracted separately into
`lean/Exec/Generated/`.

**Primary plan (decided by probe P0.1):**
- **Validator pass:** the existing `llbc` target gains
  `--exclude 'itasca::runtime'`. `extract-check` proves the output is unchanged.
- **Runtime pass:** a new `llbc-exec` target runs Charon with
  `--start-from 'itasca::runtime'`.
  - It marks validator items opaque (`--opaque 'itasca::code'`,
    `'itasca::stream'`, `'itasca::module'`, and so on).
  - Aeneas emits `Exec/Generated/{Types,Funs}.lean` and an external template.
  - The handwritten `Exec/Generated/FunsExternal.lean` (and `TypesExternal.lean`,
    if Aeneas requests one) maps each opaque validator item to the existing
    `Itasca.*` definition, for example
    `@[rust_fun "itasca::stream::validate_streaming"] def ... := Itasca.stream.validate_streaming ...`.
- **Flag names:** confirm `--start-from` and `--opaque` against the pinned
  Charon's `--help` before relying on them.

**Fallback:** if Aeneas cannot map an external trait (for example `OpVisitor`)
to an existing Lean structure, use one extraction of the whole crate. In that
case:
- `Itasca/Generated/Funs.lean` grows, and runtime edits rebuild validator proofs.
- Runtime proofs still live in `lean/Exec/`.
- Measure the rebuild cost before accepting this fallback.

`check_externals.py` gains an argument naming the model file, so both template
and model pairs are checked. `make extract` and `make extract-check` handle both
passes.

## 6. Rust implementation

### 6.1 Source layout

```text
src/runtime/
  mod.rs            Public re-exports, Value, Trap, ExecError, LinkError, ResourceLimit.
  platform.rs       Platform, FloatOps, MemoryBuffer, Alloc traits; InterruptAction; HostError.
  native.rs         #[cfg(not(charon))]: NativeFloat, StdAlloc, VecMemory, public wrappers.
  value.rs          Slot encoding: refs, v128 halves, Value <-> slots.
  bytecode.rs       Instr, CompiledFunction, side tables, well_formed.
  compiler/
    mod.rs          compile, CompileLimits, CompileError, scheduler/source glue.
    control.rs      Label stack, fixups, branch lowering (copies + jumps).
    lower.rs        Opcode -> Instr lowering for scalar, memory, table, reference ops.
    simd.rs         SIMD lowering.
  interp/
    mod.rs          Execution, invoke_with, the dispatch loop, step.
    control.rs      Calls, returns, call_indirect, branches.
    int.rs          Integer ops on slots (all proven, no premises).
    float.rs        Float ops: exact ops in integer code; rounding ops via FloatOps + NaN canonicalization.
    memory.rs       Loads, stores, size, grow; little-endian byte assembly.
    table.rs        Table and reference ops.
    bulk.rs         memory/table fill, copy, init; data/elem drop.
    simd.rs         Lane ops over two-slot values.
    host.rs         Host call marshalling, result checking.
  store.rs          Store<M>, object kinds, public store API (T6 surface).
  instantiate.rs    Allocation, const-expr and segment init via the interpreter, start.
```

**Removed:**
- fuel, `add_fuel`, and cost accounting;
- `Outcome`, `HostRequest`, `Host`, `resume_host`, `run_with_host`, `restart`;
- the tagged operand stack;
- `numeric.rs` and the old `simd.rs` (their logic moves into `interp/`).

The `libm` dependency moves behind `native.rs`.

Under `cfg(charon)`, `runtime` is now compiled (the `#[cfg(not(charon))]` on
`pub mod runtime` in `src/lib.rs` moves down to `native.rs`).

### 6.2 Platform traits

```rust
/// What the interrupt hook asks the interpreter to do.
pub enum InterruptAction { Continue, Terminate }

/// A host function failure.
pub enum HostError { Trap, StackOverflow }

/// Embedder hooks called synchronously during execution.
pub trait Platform<M: MemoryBuffer> {
    /// Polled at loop headers and function entry. Must not mutate Wasm state.
    fn interrupt(&mut self) -> InterruptAction;
    /// Executes host function `host_id`. `results` has the callee's result arity.
    fn call_host(
        &mut self,
        store: &mut Store<M>,
        host_id: u64,
        args: &[Value],
        results: &mut [Value],
    ) -> Result<(), HostError>;
}

/// Linear memory backing storage.
pub trait MemoryBuffer {
    fn bytes(&self) -> &[u8];
    fn bytes_mut(&mut self) -> &mut [u8];
    /// Grows to `new_len` bytes, zero-filling. Returns false and changes nothing on failure.
    fn grow(&mut self, new_len: usize) -> bool;
}

/// IEEE operations that round. Inputs and outputs are raw bits.
pub trait FloatOps {
    fn f32_add(a: u32, b: u32) -> u32;
    // ... full list in section 6.4
}

/// Fallible reservation, internal to the crate.
pub(crate) trait Alloc {
    fn reserve<T>(v: &mut Vec<T>, additional: usize) -> bool;
}
```

The extracted entry points are generic:

```rust
pub(crate) fn invoke_with<M, P, F, A>(exec: &mut Execution, store: &mut Store<M>, platform: &mut P,
                                      func: FuncAddr, args: &[Value], results: &mut Vec<Value>)
    -> Result<(), ExecError>
where M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc;
```

`native.rs` defines the public wrappers, for example
`Execution::invoke(&mut self, store, platform, func, args, results)`. Each calls
`invoke_with::<M, P, NativeFloat, StdAlloc>`. Wrappers contain no other logic.

**Probe P0.2 confirms these points:**
- Generic trait methods with `&mut Store<M>` arguments extract.
- An associated generic method (`reserve<T>`) extracts. If not, use one
  `reserve_*` method per element type.
- The `match` loop extracts.

**Reentrancy:** inside `call_host`, the embedder may run
`Execution::new(...).invoke(store, self, ...)`, reborrowing `self` and `store`.
The outer execution's frames live in its own `Execution`, which the hook cannot
reach.

### 6.3 Values, slots, and frames

**Slot encoding.** A slot is `u64`:

| Type | Encoding |
| --- | --- |
| `i32`, `f32` | Low 32 bits; upper bits zero. |
| `i64`, `f64` | All 64 bits. |
| `v128` | Two consecutive slots, low half first. |
| `funcref` | `0` for null, else `addr + 1`. |
| `externref` | `0` for null, else extern address `+ 1`. |

Zero bits are the default value of every type, so local initialization is a
slot fill with zero.

**Execution state:**

```rust
pub struct Execution {
    slots: Vec<u64>,        // all frames' locals and operands
    frames: Vec<Frame>,
    host_args: Vec<Value>,  // reused host-call argument buffer
    host_results: Vec<Value>,
}
struct Frame { func: u32, instance: u32, pc: u32, base: u32 }
```

**Frame layout:**
- A function's frame is `slots[base .. base + slot_count]`.
- Locals, including parameters, occupy the first `local_slots` slots.
- Operand stack position `h` (measured in slots) is at `base + local_slots + h`.
  This is fixed at compile time, because Wasm stack heights are static.

**Calls:**
- The caller's arguments are already at the top of its operand slots. Those
  slots become the callee's first locals, so arguments are never copied.
- The callee's remaining locals are zeroed. `slots` grows through `Alloc` when
  needed. Exceeding `StoreLimits` gives `Exhausted`.
- On return, results are copied to the callee's `base`. That is exactly the
  caller's operand position where the call's results belong.

### 6.4 Floating-point split

The following are implemented in Rust integer code and proven, with no premise:
- `abs`, `neg`, `copysign`;
- `eq`, `ne`, `lt`, `gt`, `le`, `ge`;
- `min`, `max`, `pmin`, `pmax` (built from comparisons and NaN/zero rules);
- reinterpretations;
- float-to-integer truncation (trapping and saturating), which is exact on the
  mantissa bits;
- `promote` (exact);
- NaN canonicalization.

`FloatOps` (premise A1) covers only rounding or rounding-like operations, for
f32 and f64:
- `add`, `sub`, `mul`, `div`, `sqrt`;
- `ceil`, `floor`, `trunc`, `nearest` (native rounding instructions are much
  faster than integer emulation);
- `demote`;
- `convert_i32_s`, `convert_i32_u`, `convert_i64_s`, `convert_i64_u`.

Each wrapper in `interp/float.rs` calls the `FloatOps` method and then
canonicalizes a NaN result. The proof needs the lemma "if the spec set contains
a NaN, it contains the canonical NaN", one instance per operation.

The SIMD float lanes call the same wrappers per lane.

### 6.5 Bytecode

Target size: 16 bytes per instruction. `Slot` is a frame-relative `u32` slot
index, and `Pc` is a `u32`. Instructions name their slots explicitly; there is no
runtime stack pointer.

```rust
pub(crate) enum Instr {
    // Moves and constants
    Copy { dst: Slot, src: Slot },
    Copy2 { dst: Slot, src: Slot },               // v128
    CopyN { dst: Slot, src: Slot, n: u32 },       // branch value transfer; dst <= src
    Const32 { dst: Slot, value: u32 },
    Const64 { dst: Slot, value: u64 },
    ConstV128 { dst: Slot, pool: u32 },

    // Control
    Jump { target: Pc },
    JumpIfZero { cond: Slot, target: Pc },
    JumpIfNonZero { cond: Slot, target: Pc },
    JumpTable { index: Slot, start: u32, len: u32 },   // side table of Pcs; default last
    LoopHead,                                          // interrupt check; back-edge target
    Call { func: u32, base: Slot },                    // func: module function index
    CallIndirect { entry: u32, index: Slot, base: Slot }, // entry: (table, type) side table
    Return { src: Slot, n: u32 },
    Unreachable,
    Select { a: Slot, b: Slot, cond: Slot },           // result in a
    Select2 { a: Slot, b: Slot, cond: Slot },

    // Variables
    GlobalGet { dst: Slot, global: u32 }, GlobalGet2 { dst: Slot, global: u32 },
    GlobalSet { src: Slot, global: u32 }, GlobalSet2 { src: Slot, global: u32 },

    // Numeric: one variant per operator, each { dst, a, b } or { dst, a }.
    I32Add { dst: Slot, a: Slot, b: Slot },
    // ...
    I32Eqz { dst: Slot, a: Slot },
    // ...

    // Memory: one variant per width/sign
    I32Load { dst: Slot, addr: Slot, offset: u32 },
    // ...
    I32Store { addr: Slot, value: Slot, offset: u32 },
    // ...
    MemorySize { dst: Slot }, MemoryGrow { dst: Slot },   // dst holds delta, then result
    MemoryFill { d: Slot }, MemoryCopy { d: Slot }, MemoryInit { d: Slot, data: u32 },
    DataDrop { data: u32 },

    // Tables and references
    TableGet { dst: Slot, index: Slot, table: u32 }, TableSet { index: Slot, value: Slot, table: u32 },
    TableSize { dst: Slot, table: u32 }, TableGrow { dst: Slot, table: u32 },
    TableFill { d: Slot, table: u32 }, TableCopy { d: Slot, entry: u32 }, TableInit { d: Slot, entry: u32 },
    ElemDrop { elem: u32 },
    RefNull { dst: Slot }, RefIsNull { dst: Slot, a: Slot }, RefFunc { dst: Slot, func: u32 },

    // SIMD: one variant per operator over two-slot values; lanes and shuffles use pools.
    // ...
}
```

**Notes:**
- Flat per-operator variants give one dispatch jump. Generate repetitive
  variants and their handlers with `macro_rules!`; macros expand before Charon.
- Fused or immediate-operand forms (for example `I32AddImm`) and local-operand
  folding are milestone M11.
- In baseline lowering, operands are at the static stack top, so `dst == a`
  for binary operators.
- Bulk operations take their operand block starting at `d` (destination,
  value/source, length in consecutive slots).

**Branch lowering:**
- A branch whose values are already in place (`n == 0`, or source equal to
  destination) is a bare `Jump`/`JumpIf*`.
- Otherwise it is `CopyN` followed by `Jump`. `br_if` with a copy becomes
  `JumpIfZero` over a `CopyN; Jump` pair.
- `br_table` entries point to per-entry stubs that do their own copies.
- `block` and `end` emit nothing. `loop` emits `LoopHead` at its start, which is
  where every back-edge lands. `if` emits `JumpIfZero` to the else arm or the
  end. `else` emits `Jump` to the end.

`CompiledFunction` holds:
- `type_index`;
- `local_slots`, `param_slots`, `slot_count`;
- `code: Vec<Instr>`;
- `jump_tables: Vec<Pc>`, `v128_pool: Vec<u128>`;
- `indirect: Vec<(u32, u32)>` (table and type indices for `CallIndirect`);
- `source_offsets: Vec<usize>`.

`well_formed` checks every Pc, side-table index, and slot against
`slot_count`. It is a cheap gate; the proofs do not rely on it.

### 6.6 Compiler

- Keep driving compilation through the validator's streaming visitor (as in the
  current `compile_with_limits`). T1 then follows from the validator's accepted
  traces.
- Discharge the streaming premises for `CompileSource`/`CompileScheduler`
  (`StreamSource.Coherent`, `StreamScheduler.Provenance`) in
  `Exec/Code/Stream.lean`. Do not modify the validator's contiguous adapter.
- Track the static slot height. The validator's `OpIterState.vals` gives value
  types, and v128 counts two slots. First confirm in `src/code.rs` whether a
  callback observes the stack before or after the operator's effect.
- Unreachable code emits nothing.
- Fixups and the label stack are as today, adapted to slot heights.
- Record, per function, the maximum slot height plus locals as `slot_count`.
- Also compile constant expressions and segment initialization into small
  synthetic bytecode sequences (section 6.8).

### 6.7 Interpreter loop

```rust
loop {
    match step::<M, P, F, A>(exec, store, platform)? {
        Flow::Continue => {}
        Flow::Done => return Ok(()),
    }
}
```

**`step`:**
- Marked `#[inline(always)]`. It loads the current frame's code and executes one
  instruction.
- Calls, returns, and host calls happen inside `step`. They update `exec.frames`
  and the current frame's pc.
- The current function's code reference is re-fetched each step. A cached-frame
  inner loop is milestone M11, and it needs a borrow-across-loop extraction
  probe.

**Proof consequence:**
- `step` has an ordinary terminating Lean model.
- The loop is proven equal to iterating `step` until `Done` or an error, which
  is partial correctness.
- T7 is stated over that iteration.
- Probe P0.4 checks how the pinned Aeneas extracts this loop.

**Memory accesses:**
- Re-fetch `store.mems[i].buf.bytes()` or `bytes_mut()` per instruction.
- The effective address is computed in `u64` and checked against the slice
  length.
- Bytes are assembled little-endian with shifts and ors.

**Host calls:**
1. Decode argument slots into `exec.host_args`.
2. Size `exec.host_results` to the arity.
3. Call `platform.call_host(store, id, &exec.host_args, &mut exec.host_results)`.
4. Type-check the results against the callee type, including store ownership of
   references.
5. Encode the results into the slots.
6. Re-fetch everything derived from the store.

**Interrupts:** `LoopHead` and function entry call `platform.interrupt()`.
`Terminate` returns `Err(ExecError::Terminated)` with all completed effects
retained.

### 6.8 Store and instantiation

**Store layout:**

```rust
pub struct Store<M: MemoryBuffer = VecMemory> {
    id: usize,
    limits: StoreLimits,
    funcs: Vec<FuncInst>,       // Wasm { instance, index } | Host { ty: TypeId, id: u64 }
    tables: Vec<TableInst>,     // { ty, elems: Vec<u64> }   (encoded refs)
    mems: Vec<MemInst<M>>,      // { ty, buf: M }
    globals: Vec<GlobalInst>,   // { ty, lo: u64, hi: u64 }
    elems: Vec<ElemInst>,       // { ty, refs: Vec<u64> }
    datas: Vec<DataInst>,       // { bytes: Vec<u8> }
    instances: Vec<Instance>,   // address lists per index space, type ids, exports
    types: Vec<FuncType>,       // interned canonical signatures; TypeId indexes this
    externs: Vec<u64>,          // extern identities
}
```

- Spec addresses equal these vector indices.
- Handles keep their store id check.
- Interning invariant: equal `TypeId` holds exactly when the structural types
  are equal. `call_indirect` relies on it.

**Instantiation follows `fun_instantiate`'s order:**
1. Resolve and check imports.
2. Allocate functions, tables, memories, and globals.
3. Evaluate global initializers and element expressions with the interpreter, on
   synthetic code.
4. Run the 2.0 initialization sequence (`table.init`/`elem.drop` per active
   element segment, `elem.drop` per declarative segment, then
   `memory.init`/`data.drop` per active data segment) as synthetic bytecode
   through `invoke_with`.
5. Call start.

Wasm 1.0 performs the bounds pre-check before step 4 and fails without writes.

Reusing the interpreter makes T2 a corollary of the T3 machinery.

`define_memory(ty, buf: M)` takes the embedder buffer. SpiderMonkey supplies an
ArrayBuffer-backed `M`.

### 6.9 Extraction rules for runtime code

The DEVELOPMENT.md constraints apply:
- safe Rust, `core`, and `alloc::vec::Vec`;
- explicit loop counters; no iterators, closures, `.clone()`, labeled control
  flow, or `String`.

Runtime-specific additions:
- Bitwise operations are allowed in runtime code (probes showed they extract).
  Keep them out of validator code.
- Indexing panics are acceptable. T4 proves them unreachable. Do not add
  `Result` plumbing only to avoid indexing.
- No `unsafe` outside `native.rs` and embedder implementations.
- Avoid `Slice::last_mut` and `Vec::truncate`. If they are needed, add concrete
  models to `Exec/Generated/FunsExternal.lean`.
- Avoid the `br_table` borrow-join pattern found earlier. Read the table index
  into a local before selecting the entry.

### 6.10 Tests, fuzzing, and benchmarks

- **[B]** Port `tests/runtime_wast.rs` and `tests/support/runtime_wast.rs` to the
  new API. Totals stay frozen. Timeouts use a counting `interrupt` that
  terminates after a large count; a termination is a failure.
- **[B]** Port `tests/runtime_api.rs`:
  - drop fuel, resume, and restart tests;
  - add host reentrancy through `call_host`, interrupt termination, embedder
    `MemoryBuffer` growth, and stack-overflow error propagation.
- **[B]** Delete `tests/runtime_resume.rs`. Port `runtime_adversarial.rs` and
  `runtime_differential.rs`.
- **[B]** Update the fuzz targets (`runtime_*`, `wasm*_execute`). Wasmi
  comparisons run without fuel and use an interrupt count limit.
- **[B]** Update `examples/runtime_bench.rs`: remove fuel, report slot and
  instruction sizes, and keep the existing workloads. Record a new baseline in
  `docs/benchmarks/`.
- Unit tests for the integer float helpers:
  - exhaustive over all f32 bit patterns for unary exact operations, run in
    release mode behind `#[ignore]`;
  - randomized for binary operations.

## 7. Lean proof architecture

### 7.1 Libraries and layering

```text
lean/
  SpecTec/                 generated
    Wasm2Prefix.lean
    wasm2.0.lean           imports Wasm2Prefix, SpecExt.Builtins
    Wasm2Builtins.lean     generated signature pins
  SpecExt/                 handwritten specification additions (trusted)
    Builtins.lean          umbrella import
    Builtins/{Bits,Int,Bytes,Lanes,Misc}.lean
    Builtins/Float/{Repr,Round,Arith,Convert}.lean
    Builtins/Examples.lean test vectors checked by `decide`/`rfl`
    Host.lean              StepH, StepsH, host events
    Wasm1.lean             Wasm 1.0 instantiation failure statement
    Audit.lean
  Itasca/                  validator (unchanged)
  Exec/                    execution proofs
    Generated/{Types,Funs,FunsExternal}.lean
    Platform/{Float,Memory,Host,Interrupt,Alloc,Recording}.lean
    Spec/{Context,Steps,Wf,Extend,Depth,Events}.lean
    Abs/{State,Decode,Step,Typing,Measure}.lean
    Abs/Sim/{Basic,Numeric,Variable,Control,Call,Memory,Table,Bulk,Simd,Host}.lean
    Code/{Layout,Rel,Stream,CompileInv}.lean
    Code/Compile/{Control,Scalar,Memory,Table,Simd,Function,Module}.lean
    Interp/{Rel,Loop}.lean
    Interp/Step/{Control,Call,Int,Float,Memory,Table,Bulk,Simd,Host}.lean
    Interp/Numeric/{Int,Float,Bytes,Lanes}.lean
    Store/{Decode,Inv,Api,Instantiate,Link,Wasm1}.lean
    Theorems/{Premises,Compile,Instantiate,Invoke,Safety,Divergence,Api}.lean
    Examples/
    Audit.lean
```

`lakefile.lean` gains `lean_lib SpecExt` and `lean_lib Exec`. `Wasm2Prefix` and
`Wasm2Builtins` join `SpecTecGenerated`. `Itasca` stays the default target.
`make prove` builds `Itasca`. A new `make prove-exec` (and `just prove-exec`)
builds `SpecExt` and `Exec` with their audits. `make verify` runs both.

**Import rules**, enforced by an extended `check_audit.py` (parametrized by root
library, each with its own `Audit` module and layer table):

| Layer | May import |
| --- | --- |
| `SpecExt.Builtins.*` | `Wasm2Prefix`, Lean, Batteries, Mathlib |
| `SpecExt.Host`, `SpecExt.Wasm1` | `«wasm2.0»`, `SpecExt.Builtins` |
| `Itasca.*` | Unchanged rules. Never `Exec.*` or `SpecExt.*` directly. `«wasm2.0»` brings in `SpecExt.Builtins` transitively. |
| `Exec.Spec` | SpecTec, `SpecExt`, `Itasca.Spec`, `Itasca.Support` |
| `Exec.Abs` | `Exec.Spec`, `SpecExt`, `Itasca.Spec` |
| `Exec.Generated` | Aeneas, `Itasca.Generated` (external mapping only) |
| `Exec.Platform` | `Exec.Generated`, `Exec.Spec`, `SpecExt` |
| `Exec.Code` | `Exec.Generated`, `Exec.Abs`, `Exec.Spec`, any `Itasca.*` |
| `Exec.Interp` | `Exec.Generated`, `Exec.Platform`, `Exec.Abs`, `Exec.Code`, `Exec.Spec` |
| `Exec.Store` | `Exec.Generated`, `Exec.Platform`, `Exec.Spec`, `Exec.Interp` |
| `Exec.Theorems`, `Exec.Examples` | Anything above |

`Exec.Abs` deliberately has no Rust dependency. The abstract machine and its
simulation stand on their own and survive Rust refactors.

**Audit requirements:**
- `Exec.Audit` and `SpecExt.Audit` use the same axiom allowlist as `Itasca.Audit`
  (`propext`, `Classical.choice`, `Quot.sound`).
- The audit also rejects `opaque` declarations in `SpecExt.Builtins` once
  milestone M7 completes.
- Optional check in `Itasca.Audit`: no validator theorem's transitive constants
  mention a `SpecExt` name. This documents that validator guarantees do not
  depend on the builtins.

### 7.2 Builtins (`SpecExt/Builtins/`)

Definitions are transcribed from `vendor/spectec/document/core/exec/numerics.rst`:

- **`Bits.lean`:** `ibits_`, `inv_ibits_`, and `fbits_`/`inv_fbits_` (via the
  `fN` representation). Bit lists are little-endian as in the prose.
- **`Int.lean`:**
  - bitwise ops: `iand_`, `ior_`, `ixor_`, `inot_`, `iandnot_`, `ibitselect_`;
  - shifts and rotates: `ishl_`, `ishr_`, `irotl_`, `irotr_`;
  - bit counts: `iclz_`, `ictz_`, `ipopcnt_`;
  - width changes: `extend__`, `wrap__`, `narrow__`;
  - SIMD helpers: `iavgr_`, `iq15mulr_sat_`;
  - the rest: `truncz`, `s33_to_u32`, `irev_`.

  Define on `Nat` arithmetic modulo `2^N` where the prose does. Use the prose's
  bit-list definitions where it defines them that way.
- **`Bytes.lean`:** `ibytes_`, `fbytes_`, `nbytes_`, `vbytes_` and their inverses.
  Little-endian.
- **`Lanes.lean`:** `lanes_`, `inv_lanes_`.
- **`Misc.lean`:** `inv_concat_`.
- **`Float/Repr.lean`:**
  - `fN` value semantics: finite values as `Rat`, plus signed zero, infinity,
    and NaN;
  - `signif`, `expon`, `canon`, NaN classes (canonical, arithmetic).
- **`Float/Round.lean`:** round-to-nearest-even from `Rat` (and from a
  `sqrt` characterization) to `fN`, with overflow to infinity.
- **`Float/Arith.lean`:**
  - arithmetic: `fadd_`, `fsub_`, `fmul_`, `fdiv_`, `fsqrt_`;
  - min/max: `fmin_`, `fmax_`, `fpmin_`, `fpmax_`;
  - sign ops: `fabs_`, `fneg_`, `fcopysign_`;
  - rounding to integral: `fceil_`, `ffloor_`, `ftrunc_`, `fnearest_`;
  - comparisons `feq_` through `fne_`.

  Results that are NaN sets follow the prose's `nans_N`. Lists may be large;
  proofs use membership lemmas, never evaluation.
- **`Float/Convert.lean`:** `convert__`, `demote__`, `promote__`, `trunc__`,
  `trunc_sat__`, `reinterpret__`.
- **`Examples.lean`:** spec-test vectors for every family, especially rounding
  ties, subnormals, signed zero, and NaN sets. Use `decide` or `rfl` only, never
  `native_decide`.

The authoritative builtin list is the split script's output. Every name needs a
definition, an example, and [R] review.

### 7.3 Host extension (`SpecExt/Host.lean`)

```lean
inductive HostEvent
  | call (fa : funcaddr) (args : List val) (out : Option (List val))  -- none = trap

inductive StepH : config → List HostEvent → config → Prop
  | step : Step c c' → StepH c [] c'
  | host_return :  -- s.FUNCS[fa] is HOST id with type t1 → t2; args : t1
      Extend_store s s' → ResultsTyped s' t2 res →
      StepH ⟨⟨s, f⟩, vals args ++ [CALL_ADDR fa]⟩ [.call fa args (some res)] ⟨⟨s', f⟩, vals res⟩
  | host_trap :
      Extend_store s s' →
      StepH ⟨⟨s, f⟩, vals args ++ [CALL_ADDR fa]⟩ [.call fa args none] ⟨⟨s', f⟩, [TRAP]⟩
  | ctxt_label | ctxt_frame | ctxt_instrs  -- copies of Step's three context rules, over StepH

inductive StepsH : config → List HostEvent → config → Prop  -- reflexive-transitive, labels concatenated
```

The final constructors follow the generated `Step` exactly, including the
`wf_config` premises.

### 7.4 Spec lemma library (`Exec/Spec/`)

- **`Context.lean`:** `StepsH` lifts through `LABEL_`, `FRAME_`, and the value
  and instruction contexts. Composing contexts.
- **`Steps.lean`:** transitivity, label concatenation, single-step introduction.
- **`Wf.lean`:** constructors for `wf_config`, `wf_admininstr`, and `wf_val`
  from component facts. This is used in every simulation case.
- **`Extend.lean`:**
  - `Extend_store` is reflexive and transitive;
  - appending objects is an extension;
  - mutating mutable globals, memory contents, and table contents (with sizes
    nondecreasing) is an extension.
- **`Depth.lean`:** the `FRAME_` nesting depth of a config (for T4).
- **`Events.lean`:** event-list lemmas.

### 7.5 Abstract machine (`Exec/Abs/`)

The abstract machine sits between Rust and SpecTec. It runs over spec `instr`
lists with a flat value stack, an explicit label stack, and a frame stack.

```lean
structure Label where
  arity : Nat          -- branch arity (params for loop, results otherwise)
  cont  : List instr   -- loop: the loop itself; block/if: empty (resume parent)
  height : Nat         -- value-stack height at entry, minus params

structure AFrame where
  fa : funcaddr
  locals : List val
  module : moduleinst
  labels : List (Label × List instr)  -- each label with the parent code after it
  code : List instr                    -- remaining code in the innermost label
  vals : List val                      -- the frame's operand stack (flat)

structure AState where
  store : store
  frames : List AFrame
```

**`Decode.lean`:** `decode : AState → config` rebuilds the nested
`FRAME_ n f [LABEL_ m cont (vals ++ ... )]` structure. Splitting each frame's
`vals` at the label heights is the core definition.

**`Step.lean`:**
- `astep : AState → AResult`, a total function.
- `AResult` is one of: next state, done with values, trap, host call required,
  or stuck.
- The function checks types dynamically and returns stuck on mismatch.

**`Typing.lean`:** `ATyped σ` means the following:
- each frame's code, with its label stack, is typed under the frame's context
  (derived from the module and the validator's `Instrs_ok`);
- the operand values have the expected types;
- the store objects referenced through the module instance have their declared
  types.

Lemmas:
- **Preservation:** `ATyped σ → astep σ = next σ' → ATyped σ'`.
- **Progress:** `ATyped σ → astep σ ≠ stuck`.

These use instruction inversion from `Itasca/Spec/TypingInversion.lean`. This is
type preservation for single bodies over `instr`, plus the store-typing facts
listed above. It is much smaller than full Wasm soundness over admin
instructions.

**`Sim/*.lean`:** `astep σ = next σ' → StepsH (decode σ) [] (decode σ')`, with at
least one step. There is one file per instruction family. Host steps produce one
event. Branch lemmas unwind `l` labels by induction (`br_succ`, then `br_zero`).

**`Measure.lean`:** the stutter measure used by T7.

### 7.6 Compiler correctness (`Exec/Code/`)

- **`Layout.lean`:** the slot layout. A function of the local types and the
  static value-type stack. It gives each stack position's slot index and width.
- **`Rel.lean`:** `CodeRel C instrs code pc labels`.
  - It is inductive over the instruction list. Each constructor states the
    bytecode emitted at `pc` and the static label context, including each
    label's continuation Pc and result slots.
  - Branches relate to `CopyN; Jump` or a bare jump, by the rules in
    section 6.5.
  - `ModuleRel m exe` lifts this to all functions, plus the synthetic
    initialization code.
- **`Stream.lean`:** `CompileSource`/`CompileScheduler` satisfy the streaming
  premises, so the validator's driver theorems apply.
- **`CompileInv.lean`:** the invariant of `FunctionCompiler` over the callback
  trace.
  - The trace is given by `Itasca.Wasm2.Trace.Correspondence` and
    `Itasca.Wasm1.Trace.*`.
  - The invariant relates the emitted prefix, open frames, and pending fixups to
    a `CodeRel` with holes.
  - It is preserved per callback.
- **`Compile/*.lean`:** per-callback preservation lemmas, then the function and
  module results (T1).

### 7.7 Interpreter refinement (`Exec/Interp/`)

**`Rel.lean`:** `IRel exec st σ` means:
- `decodeStore st = σ.store`;
- each Rust frame matches an `AFrame` by `CodeRel`, its pc, and its slots:
  `slots[base + layout i] = encode (vals or locals)[i]`;
- `ATyped σ`.

**`Step/*.lean`:** if `IRel exec st σ` and the Rust `step` returns `Continue` with
new state `(exec', st')`, then either:
- `IRel exec' st' σ'` with `astep σ = next σ'`; or
- the step stuttered: `IRel exec' st' σ` holds and the measure decreased.

Host calls apply the A2 premise and the runtime result check. Interrupts take
the `Terminated` path.

**`Numeric/*.lean`:**
- Rust integer functions equal the `SpecExt` builtins.
- Float wrappers land in the builtin result sets under A1.
- Byte assembly equals `nbytes_`/`inv_nbytes_`, and lane functions equal
  `lanes_`.

**`Loop.lean`:** the loop iterates `step`. This gives partial correctness and
the iteration count used by T7.

### 7.8 Platform premises (`Exec/Platform/`)

- **`Float.lean`:** `FloatOpsCorrect`, one field per `FloatOps` method (A1).
- **`Memory.lean`:** `MemoryLaws` (A3). Proof that `VecMemory` satisfies it.
- **`Host.lean`:** `HostSound` (A2), stated over the extracted `call_host` model.
- **`Interrupt.lean`, `Alloc.lean`:** no premises. These state that theorems
  quantify over all implementations.
- **`Recording.lean`:** the `Recording P` wrapper and the lemma that it does not
  change behavior.
- `Theorems/Premises.lean` restates every premise in one place for review.

### 7.9 Store (`Exec/Store/`)

- **`Decode.lean`:** `decodeStore`, `decodeVal`.
- **`Inv.lean`:** `Inv`. It covers:
  - well-formedness;
  - interning injectivity;
  - instance index spaces in bounds;
  - global, table, and element values typed;
  - handle store ids;
  - `StoreLimits` accounting.
- **`Api.lean`:** T6, per public function.
- **`Instantiate.lean`, `Link.lean`, `Wasm1.lean`:** T2 and the T5 link
  statement.

## 8. Milestones

Each milestone ends with `cargo test`, `cargo test --no-default-features`,
`just extract-check`, `just prove`, `just prove-exec`, and `git diff --check`
passing, plus a benchmark run if Rust changed.

### M0. Probes and plumbing

Go/no-go decisions; no runtime behavior changes.

1. **[D] P0.1 extraction split.** Reduced crate with a visitor trait in one
   module and an implementing compiler in another.
   - Show the two-pass Charon setup (section 5).
   - Show that external trait and type mapping to existing Lean definitions
     works.
   - Decide primary versus fallback.
2. **[D] P0.2 platform shape.** Reduced interpreter with:
   - generic `Store<M>`;
   - `Platform::call_host(&mut self, &mut Store<M>, ...)`;
   - `FloatOps` static methods and a generic `Alloc::reserve<T>`;
   - a `match` dispatch `step` and an outer loop;
   - slot indexing, and a `JumpTable` read pattern.

   Extract, compile, and inspect for axioms.
3. **[D] P0.3 loop model.** Confirm how the pinned Aeneas models the outer
   `loop`, and the induction principle it provides.
4. **[B] Spec split.**
   - Implement `spec_split.py` and its Makefile wiring.
   - Add `SpecExt/Builtins/*.lean` with handwritten `opaque` placeholders
     matching the generated signatures.
   - Add the `lakefile` entries and `Wasm2Builtins.lean`.
   - Acceptance: `just spec-check` and `just prove` pass, and validator theorem
     statements are unchanged.
5. **[B] Audit tooling.** Generalize `check_audit.py` to multiple roots with the
   layer table in section 7.1. Add `SpecExt/Audit.lean` and `Exec/Audit.lean`,
   and the `prove-exec` and `audit-imports` targets for both.
6. **[B] Host funccode patch.** Add `patches/spectec-wasm2-hostfunc.patch`
   (section 4.3) and its patch target. Acceptance: `just spec-update`,
   `just spec-check`, and `just prove` pass.

### M1. New Rust runtime (no proofs)

The full runtime is rewritten to section 6, and old code is deleted.

1. **[D]** `platform.rs`, `value.rs`, `bytecode.rs` type definitions, and the
   `Execution`/`Store` skeletons. Fix names and signatures first.
2. **[B]** `native.rs`: `NativeFloat` (native ops plus `libm`), `StdAlloc`,
   `VecMemory`, public wrappers.
3. **[D]** `compiler/control.rs`: slot heights, label stack, fixups, branch
   lowering.
4. **[B]** `compiler/lower.rs` and `compiler/simd.rs`: per-opcode lowering tables
   (macro-generated).
5. **[D]** `interp/mod.rs` and `interp/control.rs`: the loop, `step`, calls,
   returns, `call_indirect`, interrupts, host marshalling.
6. **[B]** `interp/int.rs`, `memory.rs`, `table.rs`, `bulk.rs`, `simd.rs`: handler
   bodies. Port the logic from the old `numeric.rs`/`simd.rs`/`execution.rs`,
   adapted to slots.
7. **[B]** `interp/float.rs`: integer implementations of the exact operations
   (section 6.4), wrappers with NaN canonicalization, exhaustive f32 unit tests.
8. **[B]** `store.rs` and `instantiate.rs`: object layout, API, interning,
   synthetic initialization code, Wasm 1.0 pre-check.
9. **[B]** Tests, fuzzers, and benchmarks per section 6.10.
10. **[B]** Rewrite `docs/EXECUTION.md` and `docs/EXECUTION_NUMERICS.md` for the
    new API. Keep the original benchmark baseline files for comparison.

Acceptance:
- the WAST corpora pass with frozen totals;
- the fuzzers run clean for an agreed time budget;
- benchmark execution medians improve on the current runtime for every
  instruction-heavy workload;
- the runtime extracts (`llbc-exec`) with no unmodeled externals.

### M2. Spec foundation

1. **[B]** `Exec/Spec/{Context,Steps,Wf,Extend,Depth,Events}.lean`.
2. **[D]** `SpecExt/Host.lean` (`StepH`, events).
3. **[B]** `SpecExt/Builtins/{Bits,Int,Bytes,Misc}.lean` real definitions and
   examples. **[R]** review against `numerics.rst`.

### M3. Integer vertical slice

End-to-end proofs for a subset:
- `i32`/`i64` constants;
- locals;
- `i32.add`, `i32.sub`, `i32.eqz`, `i32.eq`, `i32.lt_u`;
- `drop`;
- `block`, `loop`, `if`, `br`, `br_if`, `return`, `call`.

Excluded from the slice: memory, tables, globals, and host functions.

1. **[D]** `Exec/Abs/{State,Decode,Step,Typing,Measure}` for the subset. The
   design must already accommodate the full instruction set.
2. **[D]** `Abs/Sim/{Basic,Control,Call}` for the subset.
3. **[D]** `Code/{Layout,Rel,Stream,CompileInv}` and `Compile/Control` for the
   subset.
4. **[D]** `Interp/{Rel,Loop}` and `Step/{Control,Call,Int}` for the subset.
5. **[D]** `Theorems/Invoke` and `Divergence` restricted by a `SubsetModule m`
   predicate.

Acceptance: T3 and T7 for subset modules with no premises (no floats, no hosts,
`VecMemory`).

### M4. Full integer, variables, memory

1. **[B]** The remaining integer operators: `Interp/Numeric/Int`,
   `Abs/Sim/Numeric`, `Compile/Scalar`. Each operator is one lemma per layer,
   following the M3 pattern.
2. **[B]** `select`, globals: `Abs/Sim/Variable`, `Interp/Step`.
3. **[D]** Memory relation and `MemoryLaws`; load/store/size/grow simulation;
   `Interp/Numeric/Bytes`.
4. **[B]** Per-width load/store lemmas.
5. **[D]** `br_table` (`JumpTable` with stubs).

### M5. Store, API, instantiation

1. **[D]** `Store/{Decode,Inv}`.
2. **[B]** `Store/Api`: T6, one theorem per public function.
3. **[D]** `Store/Instantiate`, including synthetic initialization code and
   constant expressions; T2.
4. **[B]** `Store/Link` and `Store/Wasm1`; T5 link and argument statements.

### M6. Hosts and interrupts

1. **[D]** `Platform/{Host,Recording}`; host simulation in `Abs/Sim/Host` and
   `Interp/Step/Host`.
2. **[D]** T3 with events; the depth-induction justification of A2 as a lemma
   over API-call programs (optional; at minimum, document it).
3. **[B]** T4 statements over decoded quantities; interrupt and termination
   cases.

### M7. Floats

1. **[D]** `SpecExt/Builtins/Float/{Repr,Round}`. **[R]** review.
2. **[B]** `Float/{Arith,Convert}` definitions and examples. **[R]** review.
3. **[B]** Proofs of the integer-implemented exact operations against the
   builtins.
4. **[D]** `FloatOpsCorrect`, the canonical-NaN membership lemmas, and wrapper
   proofs.
5. **[B]** Per-operator simulation lemmas.

Exit criterion: no `opaque` remains in `SpecExt.Builtins` except lane builtins
(M9). Turn on the audit rule.

### M8. References, tables, bulk operations

1. **[B]** `ref.*`, `table.*`, `elem.drop`, `data.drop`.
2. **[D]** `call_indirect` (interning invariant).
3. **[D]** Bulk memory and table operations against the 2.0 reduction rules,
   which are defined recursively per element. Optional: chunked bulk operations
   with interrupt checks between chunks.

### M9. SIMD

1. **[B]** `SpecExt/Builtins/Lanes` definitions. **[R]** review.
2. **[B]** Lane function proofs, then per-operator lemmas (236 opcodes, grouped
   by shape family as in the validator's `Wasm2/Simd/`).

### M10. Completeness side theorems

1. **[B]** The T5 grow statements and the T4 refinements, if not already done.
2. **[D]** Final statements of T1 to T7 in `Theorems/`, plus the README trust
   boundary update. **[R]** review of premises and weakenings.

### M11. Performance work (each item with proofs)

Measure each against the M1 baseline.

1. Local-operand folding: `local.get` produces no copy, and operands refer to
   local slots directly. Materialize before writes to the same local and at
   label boundaries. Extends `CodeRel` with a virtual-stack mapping.
2. Immediate-operand forms (`I32AddImm` and similar).
3. Cached frame code and memory borrows across the inner loop, if a probe shows
   the borrow pattern extracts.
4. Fused compare-and-branch.

### M12 (follow-on). Compile completeness (T8)

## 9. Documentation and policy updates

| File | Change |
| --- | --- |
| `AGENTS.md` | New coupled sources (`src/runtime` with `lean/Exec/Generated/`), the split stage, `SpecExt` rules, required checks (`just prove-exec`). |
| `DEVELOPMENT.md` | Source layout, runtime extraction constraints (section 6.9), command table. |
| `README.md` | Execution guarantees and trust boundary once M10 lands. Until then, the runtime is described as under verification. |
| `lean/README.md` | `SpecExt` and `Exec` layering and the premise list. |
| `docs/EXECUTION.md`, `docs/EXECUTION_NUMERICS.md` | Rewritten for the new API (M1). |

## 10. Risks

| Risk | Mitigation |
| --- | --- |
| External trait mapping fails in Aeneas (P0.1). | Single-extraction fallback (section 5). |
| The pinned Aeneas cannot model the outer loop usefully (P0.3). | Bounded-iteration entry point used by the proofs, with the unbounded loop as a reviewed wrapper. |
| `CompileInv` over fixups is large. | M3 slice first. Keep lowering rules uniform (section 6.5). |
| `wf_config` premises bloat every case. | `Exec/Spec/Wf.lean` builds them once per instruction shape. |
| Float spec transcription error. | Examples from the spec test suite, exhaustive f32 differential tests between native ops and a Lean-extracted reference (evidence only), and [R] review. |
| Performance regression from proof-driven structure. | M1 benchmarks gate before proofs. M11 recovers with proofs. |
| Spec split script drifts from SpecTec output format. | The script fails closed. `Wasm2Builtins.lean` pins signatures. |
