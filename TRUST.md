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
| `validate_module_typed` | **No false accepts.** If it accepts, the input is a module binary *and* WebAssembly's type system accepts the module it decodes to, with the import and export types it assigns being the ones the validator reports (below). |
| `validate_module_complete` | **No false rejects.** If the input is a module binary and the module it decodes to satisfies WebAssembly 1.0's rules, it accepts. Same qualifier as for bodies: the fixed size caps are real, and the theorem is about files under them. |
| `validate_module_typechecked` | The same with WebAssembly's own rules in place of ours: **if the input is a module binary and WasmCert's module type checker accepts the module it decodes to, this validator accepts the input**, and reports the same two extern-type lists the checker produced -- provided the module respects three restrictions Wasm 2.0 lifted (below). |

Every operator's immediates reach the consumer decoded and checked, including
`br_table`'s label vector: that one goes over one depth at a time as the loop
reads it, because collecting it first would mean a `Vec` with no bound but the
byte count, and `Vec::push` would be back on the live panic list.

Two more results, about the interface rather than the verdict. A hook per opcode
means a table turning an opcode into a hook, and a table whose rows were off by
one would validate exactly as well while handing a consumer the wrong
instruction. `visit_numeric_names_convert` and its three siblings rule that out:
for every row of both tables, the hook the fan-out picks is the one whose
mnemonic names the instruction `Spec_Binary.op_spec` gives that byte. Swap two
rows and they stop holding. `trace_records` is the same check for the 174 hooks
one at a time: it is the proof that a visitor whose every hook appends the
instruction its own name claims does record the operator stream, and it is
unprovable if any hook's name and payload disagree.

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

The same three about `validate_body_with`, which is the one a compiler runs: it
takes an `OpVisitor` and calls one hook per accepted operator, so the loop the
theorems are about is the loop the compiler runs. There is no second loop to
trust. Each carries the hypothesis its statement cannot do without, and
`validate_body` is `validate_body_with` at the do-nothing visitor, which is why
the three above hold with no hypothesis at all.

| Result | Description |
|---|---|
| `validate_body_with_no_panic` | It never crashes and never hangs, **provided every hook returns**. A hook is unverified code; nothing in its type stops it looping or panicking, and `hooks_total` says it does neither. |
| `validate_body_with_typed` | **No false accepts**, for any consumer whatsoever. No hypothesis: a run that accepted is a run whose hooks all returned `Ok`, so the bytes really do encode a well-typed function. |
| `validate_body_with_complete` | **No false rejects**, provided the consumer accepts every operator it is shown (`hooks_accept`). A consumer that declines a well-typed body stops the loop, and reporting that is the interface working. |
| `validate_body_with_trace` | **The hooks are the program.** An accepting run showed the consumer exactly the operators the body's bytes encode, in the order the bytes give them: none skipped, none repeated, none invented. The consumer says what its own state records (`records`) and the theorem says that state ends up holding the byte-level operator stream. |

`validate_body_with_trace` is the row a compiler leans on. Soundness says the
verdict is right; the trace says the hooks a compiler generates code from are
the run that earned that verdict, so there is no gap between what was checked
and what was compiled. `validate_body_trace` is the same statement at the
recording visitor, where the operator list is a value rather than a hypothesis,
and `validate_code_entry_with_sound` carries it to the per-function entry point
a compiler actually calls: the operators it was shown are the body of the code
entry those bytes encode, the frame hook aside.

Soundness is proven in three steps, and the last one is why the row above can
say "well typed". `validate_body_sound` gets to WasmCert's *decision procedure*
saying yes. `validate_body_checker` restates that in the exact form WasmCert's
own reflection lemma consumes. `validate_body_typed` applies the reflection
lemma, which is an if-and-only-if, and lands on `be_typing`: WasmCert's
specification-level typing judgement, the same relation the paper defines the
type system with.

`ModuleVisitor::on_custom_section` reports where a module's custom sections are,
from `decode_env_with` for the ones before the code section and
`decode_tail_with` for the ones after it. The decoders already read every one of
them in order to skip it, so this is what they saw and not a second walk.

It is a report and not part of the verdict: a custom section is not part of the
module a binary denotes, and `Spec_Module.v` reads the format's customs as
padding, so a wrong answer would mislead a consumer about a name and not about
whether the module is valid. Nothing says the ranges reported are the custom
sections the format says are there.

Reported rather than carried on `Env` and `Tail` for a reason worth writing
down, because it is the shape of the argument and not a detail. `chain_from`
pins a decoded `Env` field for field, from `Env::new()` through to the record
`decode_env` returns, and `chain_custom` says in as many words that a custom
section leaves the environment alone. A field the walk grew would make that
false, and the repair would be to teach the chain to erase a field no theorem
mentions before comparing. A hook keeps the decoded record describing only what
the theorems talk about, and leaves `decode_env_sound` and
`decode_env_complete` saying exactly what they said before.

The two decoders keep their `hooks_total` and `hooks_accept` obligations, as
`validate_body_with` does. `decode_env_ok` and `decode_tail_ok` are the nop
instances, so they hold with no hypothesis; a consumer that supplies a hook owes
`module_hooks_total` for no-panic and `module_hooks_accept` for completeness. As
with a body, neither can turn a rejection into an acceptance: a declining hook
stops the decode and is reported as a decline.

`CodeVisitor::on_need_bytes` is the third hook, and it is what lets a consumer
block until the bytes of the entry it is about to be shown have arrived. It is
in `code_hooks_total` and `code_hooks_accept` like any other, and it decides
nothing: the walk reports where it is about to read to and then reads the same
bytes it would have.

### Driving the walk changes nothing

Every result above is stated about the run the consumer made, which leaves the
question a compiler actually asks: how do the run it made and the run the
theorems name relate? `Module_Driven.v` and `OpIter_Driven.v` answer it, and
the whole content of both files is one observation: a hook is handed the state
and hands back a verdict, so the reader half of a dispatch branch does not
mention the visitor. An accepting run fixes the state trajectory on its own,
and any other consumer whose hooks accept walks the same one.

| Result | Description |
|---|---|
| `validate_body_with_transfer` | An accepting run of a body at one consumer is an accepting run at any consumer whose hooks accept, with the same verdict. |
| `validate_code_entry_driven` | **A compiler's own run of an entry is the validator's verdict.** If `validate_code_entry_with` accepted at the consumer's own `OpVisitor`, then `validate_code_entry` accepts the same bytes at the same position. This is the shape `code_hooks_validate` asks for, so it is what a consumer that dispatches entries to other threads discharges its obligation with. |
| `validate_code_entry_accepts` | The mirror, which discharges `code_hooks_accept`: that consumer does not refuse an entry the validator accepts. |
| `validate_module_with_accepts` | The mirror of `validate_module_driven`, one level up: a module `validate_module` accepts is one the driven walk accepts, reporting the same `ValidatedModule`. Together the two say driving changes neither the verdict nor the result. |
| `validate_module_with_no_panic` | The driven walk terminates, given `module_hooks_total` and `code_hooks_total`. |
| `validate_module_with_complete` | And it does not reject a valid module, given the two `_accept` obligations. |

Without `validate_code_entry_driven` the interface would have had a hole where
its main use is: `code_hooks_validate` is a claim about `validate_code_entry`,
the do-nothing run, and a compiler runs `validate_code_entry_with` at its own
visitor. Nothing else relates the two.

### A module held in pieces

`validate_module_parts` says an accepting `validate_module` is three accepting
parts. `validate_module_of_parts` is the converse, and it is the one a
streaming consumer needs: three accepting parts *are* an accepting
`validate_module`, on the same bytes, with the same `ValidatedModule`. So a
consumer that called `decode_env`, `validate_code` and `decode_tail` itself
inherits `validate_module_repr`, `validate_module_typed` and
`validate_module_typechecked` rather than having them restated for it.
`validate_module_parts_typed` is that composition written out once: three
accepting parts mean the bytes are a well-typed Wasm 1.0 module, with the
import and export types the environment reports.

Two conditions come with that, and both are the caller's. The first is size:
`validate_module` checks the input is at most `MAX_MODULE_BYTES` long and then
calls the parts, which is why it has no hypothesis at all, and every no-panic
and completeness result about a *part* carries the bound instead. A consumer
that calls the parts itself owes the check. The bound guards `usize` arithmetic
in the model rather than anything a 64-bit host can reach, but it is a
hypothesis and not a remark, and no part enforces it for itself.

The second is provenance: `env` came out of `decode_env` on the same bytes, and
each position came out of the part before it. Soundness is stated
relative to the environment handed over, so a fabricated `Env` earns a true
theorem about a module nobody has; and `env_small`, which the code section's
no-panic results need, is `decode_env`'s postcondition and nothing else's.
`Env`'s fields are public and writable, so the type system does not enforce
either.

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

- **That growing the input cannot change an answer.** A streaming consumer runs
  `decode_env` on a prefix and again on more bytes as they arrive, and nothing
  here says the two agree: there is no lemma relating a decoder's result on
  `data` to its result on `data` with more appended. Every result is about the
  bytes it was handed. In practice the decoders only ever read forward and stop
  at the code section's header, so the answer does not move, but that is an
  argument and not a theorem.

  `veriwasm_status_needs_more_input`-style logic in a shim is the same gap seen
  from the other side: `UnexpectedEof` and `MissingCodeSection` are the only
  two rejections a longer input can turn into an acceptance, and that fact is
  read off the error enum rather than proved.

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

**Your hooks, if you use `validate_body_with`.** The two hypotheses above are
assumptions about code this repository does not contain. `hooks_total` is
discharged by not panicking and not looping; `hooks_accept` by returning `Ok`.
Neither can turn a rejection into an acceptance: `validate_body_with_typed`
holds for every consumer, hostile ones included, because acceptance is decided
before a hook is ever consulted. What a bad hook can do is refuse a valid body
or fail to terminate.

**A C ABI, if a consumer builds one on top of this crate's public API.** That
glue -- SpiderMonkey's `veriwasm_glue` is one -- is unverified and outside the
Aeneas subset; nothing in this repository is fed to Charon on its behalf. One
of the two things such glue typically adds is not in any theorem: `op_offset`, the
byte offset of the operator a hook is being told about, is derived rather than
read. The validator reports the cursor after an operator's immediates, and the
cursor one hook sees is where the next operator starts; the body's base, which
turns that into an offset into the bytes the caller handed over, does come from
the validator. A caller that handed over a region rather than a whole module
re-bases it itself. It cannot change a verdict, being a position: every byte an
entry is judged on is read by `validate_code_entry` as before. The same goes for
the offset a rejected body is reported at, which is that cursor. The other thing
it adds is the pointer handling itself.

It reports nothing about its own misuse. A null pointer or an out-of-range index
aborts, so a verdict it returns is always a verdict about a module and never
about a caller's mistake.

What does *not* change is who is trusted for what. A C++ hook stands where a
Rust one stood, so `hooks_total` and `hooks_accept` are now claims about C++, and
`validate_body_with_typed` still holds for it with no hypothesis at all.

Where a consumer starts is covered too, and this is the one place the interface
asks a consumer for something beyond returning. A compiler cannot validate the
code section entry by entry in order: it has to know where entry `k` is before
the `k` before it have been validated, so it can hand them to other threads. So
`validate_code_with` frames each entry by its own size prefix and reports it
without validating it, and taking `on_code_entry` means taking on that entry's
validation.

`code_hooks_validate` is that obligation written down: the consumer's `Ok` on an
entry means `validate_code_entry` says `Ok` for the same position, index and
environment. It is a claim about a pure function of those four, so it says
nothing about when the consumer did it or on which thread.

Two results turn that into the guarantee. `code_entry_extent_frames` says the
framing step and the validator agree on where an entry ends -- they read the
same size prefix at the same position and add the same length, so it is an
equality and not an argument. `validate_code_driven` uses it to show that an
accepting driven walk is an accepting `validate_code`, position for position,
which is what lets a consumer that drove the section itself compose with
`validate_module_parts`. `validate_code_with_sound` is the same run's soundness
directly: the bytes are a well-formed, well-typed code section.

Without the framing result, `validate_code_entry_with_sound` would only say the
operators shown are the body of the entry at whatever offset the consumer
supplied, and nothing would say that offset was one the section's own framing
gives.

`validate_module_driven` carries that all the way up: a whole module driven
through the hooks is the module `validate_module` validates, with the same
verdict and the same `ValidatedModule`. So every result about `validate_module`
-- `validate_module_repr`, `validate_module_typed`, `validate_module_parts` and
the rest -- holds of a consumer that drove the module itself, and none of them
had to be restated for one. The obligation is the code section's alone: the two
decoders ask nothing of their consumer, because reporting a custom section
cannot change what is read next.

A consumer that discharges `code_hooks_validate` by running
`validate_code_entry_with` at its own visitor does not have to argue for it:
`validate_code_entry_driven` is that step, and "Driving the walk changes
nothing" above is where the rest of it lives.

**The two conditions on a decomposed run.** `validate_module` has no
precondition; the parts do, and the caller owes them. The input must be at most
`MAX_MODULE_BYTES` long, and `env` and each position must have come from the
part before. "A module held in pieces" above says what goes wrong without
either. Neither is enforced by a type, and `Env`'s fields are public and
writable.

**Coq's proof checker is correct.** Standard for all work of this kind.

**Aeneas's model of the Rust standard library.** `just trust` prints the axiom
count behind each theorem; the headline results reach 52, in three groups.

- 17 in `theories/Aeneas_Specs.v`, describing what Rust standard-library
  operations do (what `Vec::pop` returns, what indexing a slice gives you, what
  a sub-slice contains) and what two of our own derived `PartialEq` impls do.
- 10 of the 13 in `theories/Veriwasm_FunsExternal.v`, which Aeneas emits for
  library functions it does not translate. The other three are defined and
  unreached.
- 21 from Aeneas's own `Primitives.v`, which are the operations the first group
  constrains rather than descriptions of them: `slice_index_usize`,
  `slice_len`, `alloc_vec_Vec_index` and the `core_slice_index_*` family, plus
  the `usize_max` and `isize_min` bound constants. Trusting these is trusting
  that Aeneas's encoding of Rust's scalar and slice primitives is the right
  one, which is a distinct assumption from trusting that it translated our
  functions faithfully.

**Four classical mathematical axioms**, inherited from WasmCert's use of the
CompCert floating-point library.
