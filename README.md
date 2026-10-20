# itasca

***veritas caput***

A streaming WebAssembly validator written in Rust and verified in Lean.

It supports the WebAssembly 1.0 and 2.0 core profiles, including
parallel function validation and compiler callbacks. Both profiles have
whole-module termination, soundness, and completeness proofs.

The execution runtime has checked compilation, invocation, instantiation, API
invariant, resource-cause, and progress theorems for both profiles. These are
[conditional guarantees](docs/EXECUTION_VERIFICATION.md#public-theorem-map)
under explicit platform and callback contracts.

This is an experiment in AI-assisted formal verification, built extensively
with Claude and Codex. Read [formal verification](#formal-verification) for
more details.

## Usage

```rust
let bytes = b"\x00asm\x01\x00\x00\x00";
let module = itasca::validate_module(bytes, itasca::ValidationProfile::Wasm1)?;
let imports = itasca::import_types(module.env())?;
let exports = itasca::export_types(module.env())?;
```

The two profiles:

| Profile | Extensions |
| --- | --- |
| `Wasm1` | None |
| `Wasm2` | multi-value, sign extension, saturating conversions, reference types, multiple tables, bulk memory, passive and declarative segments, SIMD instructions. |

`validate_module` is internally implemented using the more powerful and complex
`validate_streaming` API. This API supports streaming reads, discontiguous
buffers, and parallel compilation of function bodies.

```rust
use itasca::{
    CodeBatch, Config, Env, Error, Region, Result, Source, StreamingVisitor, Tail,
    ValidationProfile,
};
use std::vec::Vec;

struct Input(&'static [u8]);
impl Source for Input {
    fn environment(&self) -> Result<&[u8]> { Ok(self.0) }
    fn code_len(&self) -> usize { 0 }
    fn code(&self, start: usize, end: usize) -> Result<&[u8]> {
        if start == 0 && end == 0 { Ok(&[]) } else { Err(Error::Host) }
    }
    fn tail(&self) -> Result<&[u8]> { Ok(&[]) }
}

#[derive(Default)]
struct Visitor<'a> { returned: Vec<CodeBatch<'a>> }

impl itasca::ModuleVisitor for Visitor<'_> {}

impl<'a> StreamingVisitor<'a> for Visitor<'a> {
    fn custom_region(&mut self, _region: Region) {}
    fn environment_ready(&mut self, _env: &Env) -> Result<Config> {
        Ok(Config { batch_bytes: 4096, max_batches: 2 })
    }
    fn submit_code_batch(&mut self, mut batch: CodeBatch<'a>) -> Result<()> {
        // Implementations can synchronously validate a batch, or schedule it
        // for background validation. They must call `validate_func` on all
        // entries of the batch and eventually return it via `poll_code_batch`.
        let mut count = 0;
        while count < batch.len() {
            let entry = batch.next_entry()?;
            batch.validate_func(entry.index, &mut itasca::EmptyOpVisitor)?;
            count += 1;
        }
        self.returned.push(batch);
        Ok(())
    }
    fn poll_code_batch(&mut self) -> Result<CodeBatch<'a>> {
        self.returned.pop().ok_or(Error::Host)
    }
    fn code_end(&mut self) -> Result<()> { Ok(()) }
    fn tail_ready(&mut self, _tail: Tail) -> Result<()> { Ok(()) }
}

let source = Input(b"\x00asm\x01\x00\x00\x00");
let mut visitor = Visitor::default();
let mut env = Env::new();
itasca::validate_streaming(0, ValidationProfile::Wasm1, &source, &mut visitor, &mut env)?;
```

## Formal verification

The pipeline is:

```text
Rust --Charon--> LLBC --Aeneas--> Lean program model
SpecTec Wasm 2.0 source ----------> Lean declarative judgments
Independent binary grammar ------> exact bytes and selected profile
Handwritten Lean proofs ----------> validator guarantees
```

“Accepts” means the extracted function returns ordinary `Ok`.
“Terminates” means it returns success or an error without panic, arithmetic overflow, out-of-bounds access, or divergence (allocation failure is not modeled).
“Well typed” refers to the generated SpecTec declarative judgments.
"Total" means that arbitrary bytes terminate.
"Sound" acceptance implies the bytes encode a module that is well typed.
"Complete" means that all well-typed binary encoded modules within implementation limits are accepted.

| Entry point | Guarantee |
| --- | --- |
| `validate_module` | Total, sound, and complete. |
| `validate_streaming` | Total, if callbacks are total. Sound, if source views are coherent and if Rust field-privacy of `CodeBatch` is respected. Complete, if source views spans are correct and `poll_code_batch` eventually receives all dispatched `CodeBatch`. |

The extracted execution runtime also has checked all-input compilation,
compiler completeness under conservative source eligibility and allocation
availability, and conditional public invocation and instantiation correspondence. The
[execution guarantees](docs/EXECUTION_VERIFICATION.md#public-theorem-map) records the
exact theorem scope and embedder obligations. Host-capable theorems require
allocator, floating-point, memory and callback laws, including explicit raw
metadata and reference-preservation premises. Public invocation and instantiation
recording, evolving-code invariant preservation and classified resource causes
are checked under those premises. The resource accounting, callback
obligations are documented explicitly. Public invocation additionally matches a
selected terminating source run under explicit choice compatibility, source
capacities, allocation availability, continuing interrupts and returning-host
resource laws.
For the certified combined host driver, this includes unbounded reentrancy:
one terminating chosen Wasm/host execution yields the corresponding synchronous
invocation outcome, decoded store and expanded call history. Primitive growth,
numeric, API and publication choices must match the implementation, and source
prefixes must fit the configured limits. Divergent callbacks have separate
productive combined-source traces; callback normality is not a premise of
these driver theorems. Arbitrary Rust callbacks still require an explicit
implementation refinement contract.

### Trust boundary

The proofs depend on:
  1. Rust translation into Lean by Charon and Aeneas.
  2. Aeneas's standard-library and loop models.
  3. Validation judgements generated by SpecTec.
  4. Hand-written binary grammar.
  5. The rustc compiler.
  6. Lean's kernel and standard logical foundations.

Execution additionally uses the handwritten specification extensions in
[`lean/SpecExt`](lean/SpecExt). Atomic host return and trap require post-call
`Store_ok`; the public invariant's checked typing bridge discharges that
condition for invariant-preserving callbacks. The native wrappers, standard allocator, native/libm
floating-point operations, and globally issued store identities remain reviewed
boundaries outside extraction; the generic proofs do not establish their
platform laws. See the [Lean execution boundary](lean/README.md#execution-boundary).
