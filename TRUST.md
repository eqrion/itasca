# Trust

## Summary

Validating a wasm 1.0 is proven correct wrt. the WasmCert 1.0 formalization. An
accepted `.wasm` file really is a WebAssembly 1.0 module binary, the module it
decodes to really is well typed, a valid module is not rejected, and no input
makes the validator crash (outside of OOMs).

## Pipeline

The Rust source is translated into the Coq proof assistant, mechanically, by a
tool called Aeneas. The result is a Coq function that behaves exactly like the
Rust one. We then prove things about that Coq function. Separately,
[WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq) is an existing academic
formalisation of WebAssembly. The proofs here connect the two. We show our
validator accepts exactly the programs WasmCert says are valid.

## What is proven

Five results about `validate_module`, which takes a whole `.wasm` file:

| Result | Description |
|---|---|
| `validate_module_no_panic` | It never crashes (outside of OOMs) and never hangs, on any input at all. |
| `validate_module_repr` | **If it accepts, the input really is a WebAssembly 1.0 module binary.** Every section is where the format says, framed the way the format says, and the whole file decodes to a module. |
| `validate_module_typed` | **No false accepts.** If it accepts, the input is a module binary *and* WebAssembly's type system accepts the module it decodes to. |
| `validate_module_complete` | **No false rejects.** If the input is a module binary and the module it decodes to satisfies WebAssembly 1.0's rules, it accepts. Same qualifier as for bodies: the fixed size caps are real, and the theorem is about files under them. |
| `validate_module_typechecked` | The same with WebAssembly's own rules in place of ours: **if the input is a module binary and WasmCert's module type checker accepts the module it decodes to, this validator accepts the input** -- provided the module respects three restrictions Wasm 2.0 lifted (below). |

The three restrictions it still asks for are the places WebAssembly 1.0 is
narrower than the 2.0 type system WasmCert formalises: a function type may
return at most one value, and a module may have at most one table and at most
one memory. A module breaking one of those is valid 2.0 and not valid 1.0, and
rejecting it is the validator doing its job.

Three results about `validate_body`, which takes the raw bytes of one function
body and either accepts or rejects them.

| Result | Description |
|---|---|
| `validate_body_no_panic` | It never crashes (outside of OOMs) and never hangs. On any input at all, including random, truncated or hostile bytes, it terminates and returns an answer. |
| `validate_body_typed` | **No false accepts.** If it accepts, the bytes really do encode a well-typed WebAssembly function. |
| `validate_body_complete` | **No false rejects.** If the bytes encode a well-typed function, it accepts them. This rules out the trivial "reject everything" validator. |

Soundness is proven in three steps, and the last one is why the row above can
say "well typed". `validate_body_sound` gets to WasmCert's *decision procedure*
saying yes. `validate_body_checker` restates that in the exact form WasmCert's
own reflection lemma consumes. `validate_body_typed` applies the reflection
lemma, which is an if-and-only-if, and lands on `be_typing`: WasmCert's
specification-level typing judgement, the same relation the paper defines the
type system with.

## What is not proven

- **Completeness against `module_typing` rather than the type checker.**
  `validate_module_typechecked`'s premise is WasmCert's *decision procedure*
  saying yes, not its typing judgement `module_typing`. WasmCert proves the
  module checker sound and never proves it complete, so accepting-by-the-checker
  is the stronger requirement: a module that `module_typing` admits but the
  checker rejects would fall outside our theorem.

  Function bodies do not have this gap: there WasmCert proves the checker
  reflects the typing judgement so `validate_body_complete`'s premise and
  `be_typing` are interchangeable.

## What you have to trust

**WasmCert-Coq is a faithful formalisation of WebAssembly.**

**Our transcription of the binary format is right** (`theories/Spec_Binary.v`
for instructions, `Spec_Expr.v` for expressions, `Spec_Module.v` for the module
around them). WasmCert cannot supply this: its binary-format module declares
the key definitions with no content at all, and its parser has no correctness
theorem, so proving agreement with it would only prove agreement with unverified
code. Ours is a hand transcription of the specification's tables, one-line rules
with no clever reasoning.

**That a 1.0 module is the 2.0 module we say it is.** WasmCert's `module`
type is WebAssembly 2.0-shaped, so `Spec_Module.v` has to say which 2.0 value a
1.0 binary denotes, and in two places the answer is a transform rather than a
copy: an element segment's vector of function indices becomes one `ref.func`
expression each, and a data segment's memory index becomes part of its mode.

**Aeneas and Charon translate Rust to Coq faithfully.** If the translation is
wrong, we have proven something true about a program that is not the one we
ship.

**Coq's proof checker is correct.** Standard for all work of this kind.

**Two small sets of Rust stdlib axioms require by Aeneas.** 17 in `theories/Aeneas_Specs.v`,
describing what Rust standard-library operations do (what `Vec::pop` returns,
what indexing a slice gives you, what a sub-slice contains) and what two of our
own derived `PartialEq` impls do. 13 more in
`theories/Veriwasm_FunsExternal.v`, which Aeneas emits for library functions it
does not translate.

**Four classical mathematical axioms**, inherited from WasmCert's use of the
CompCert floating-point library.
