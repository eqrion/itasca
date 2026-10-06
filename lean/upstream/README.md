# Upstream issues

The actionable submission/status tracker is [UPSTREAM.md](../../UPSTREAM.md).
This document retains the detailed local failure analysis and reproduction
commands. All findings refer to the pinned revisions below.

## Optional mutability loses the immutable case

At SpecTec commit `edc84f7ec81f927f3fdb952a82ecd38fed8e4f29`, the Wasm rule
`|- MUT? t : OK` becomes a Lean `Globaltype_ok` judgment with only a constructor
for `some MUT`. The source rule allows both mutable and immutable globals.
The unmodified output prevents a soundness theorem covering itasca's accepted
immutable globals.

The committed intermediate-language dumps locate the change in the
`remove-indexed-types` pass. In `spectec/src/middlend/undep.ml`, the `IterE`
case for `(Opt, [])` replaces optional repetition with `OptE (Some e1)`.
The same pass converts list repetition without iteration variables to a
singleton list; that adjacent case also needs semantic review.

`optional-mutability.spectec` isolates the original failure. Run
`make -C lean spec-repro` to inspect it; the general transformation bug remains.

The local workaround is
[`spectec-wasm2-global-mutability.patch`](../../patches/spectec-wasm2-global-mutability.patch).
It changes the Wasm source rule from `|- MUT? t : OK` to `|- mut t : OK`.
Since `syntax mut = MUT?`, the variable ranges over exactly the same two
possibilities. This avoids the broken optional-pattern transformation without
changing the permitted globals. Regeneration produces one constructor
quantified over mutability; `Itasca/SpecChecks.lean` now proves both cases, and
`Itasca/TypeTranslation.lean` proves validity for every extracted Rust global type.

This is a source-level workaround for this rule, not a fix for arbitrary
optional/list patterns. The neighboring list rewrite still needs review before
relying on affected judgments. No generated definition was hand-edited. The
workaround has not been submitted upstream.

## Four-byte UTF-8 range is truncated in the Wasm source

The pinned `specification/wasm-2.0/A-binary.spectec` four-byte UTF-8 rule uses
`U+10000 <= ch < U+11000`. The upper bound should be `U+110000`, matching the
Unicode scalar range already present in `1-syntax.spectec`. The generated
`fun_utf8` consequently cannot witness intended encodings such as U+1F600,
blocking name well-formedness for accepted modules with emoji names.

[`spectec-wasm2-module.patch`](../../patches/spectec-wasm2-module.patch)
corrects the source bound. `Itasca/SpecChecks.lean` proves the actual four-byte
encodings for U+10000, U+1F600, and U+10FFFF, and name well-formedness for the
emoji. This is a specification-source correction, not a Lean backend change.

## Import projection fallbacks lose their `otherwise` guards

The Wasm source projections `funcsxt`, `globalsxt`, `tablesxt`, and `memsxt`
retain matching import types and otherwise skip the head. In the pinned Lean
output the fallback lacks its `otherwise` condition. Thus, for example,
`fun_funcsxt [FUNC ft] []` is derivable as well as the intended `[ft]` result.
These weakened relations do not determine the correct module index spaces.

`otherwise-projection.spectec` minimizes this failure to KEEP/DROP tags.
`make -C lean spec-repro` generates the uncorrected reproducer alongside the
optional-mutability example. Its `fun_keeps_case_2` can drop KEEP because the
fallback has no exclusion premise.

The module source patch replaces the four fallbacks with explicit cases for
the three nonmatching external-type constructors. Regeneration then preserves
the distinction without depending on `otherwise` translation. The checked
`SpecChecks` regressions prove that a singleton matching import cannot be
discarded for any of the four projections. Module proofs additionally use
deterministic canonical projections and exact cache correspondence.

This is a local source workaround, not a general fix for backend handling of
`otherwise`. Other uses still require review before relying on them. Both
module changes regenerate through `spec-update`; generated Lean is not edited
by hand. The source patches and issue reproducers have not been published.

## Structure fields shadow namespaces in Aeneas output

At Aeneas commit `557eff83ecef5083b98a52a94ca7fae63d6c1dab`, generated
structure fields can shadow namespaces referenced in later field types. For
example, itasca's environment becomes:

```lean
structure module.Env where
  types : alloc.vec.Vec types.FuncType
  -- Other fields omitted here.
  func_types : alloc.vec.Vec types.FuncType
```

Lean resolves the second `types.FuncType` through the earlier `types` field
and reports an invalid field projection. The same problem affects
`module.Import`: its `module` field shadows `module.ImportDesc`.

Run `make -C lean aeneas-repro` to extract `namespace-shadow.rs` with the pinned
Charon and Aeneas and compile the output with Lean. The final compilation
now passes with the local source patch. The full `just lean-prove` build also
passes. A second instance affected local variables: `let types := ...` hid the
namespace in `types.ValueType.I32` later in the function.

[`aeneas-lean-extraction.patch`](../../patches/aeneas-lean-extraction.patch)
qualifies references to generated types with their root namespace, preserving
builtin names, declaration names, and references within recursive groups.
Local binder generation also reserves namespace prefixes, so the offending
local becomes `types1`. This applies only to the Lean backend.

## Deep else-if chains lose indentation in Aeneas output

Once structure types compiled, the numeric visitor dispatcher exposed a second
printing defect. Each `else if` added indentation until OCaml Format reached
its limit. Lean then parsed a continued function application as separate
statements in a `do` block.

The same Aeneas patch prints `else if` chains at a constant indentation. It
does not alter the translated expression or require a wider line-length limit.
This fixes the full validator's dispatchers.

## Regression checks and patch maintenance

`make -C lean regressions` runs Aeneas's test runner and compiles the generated
Lean. The patch includes Rust and generated Lean cases covering structure
fields, generic and recursive types, constructor references, and a 48-branch
dispatcher. The generated runtime checks verify the constructor and early,
late, and fallback dispatcher paths. The original small reproducer also checks
an explicit namespace override.

The Makefile applies the source patches idempotently and fails on incompatible
checkout changes. Both patches have been checked against clean copies of their
pinned source files. `make -C lean spec-check` verifies deterministic SpecTec
regeneration against the committed local file. Keep the upstream checkpoint
intact; use `spec-update` to refresh our generated copy after source changes.

These patches are local and have not been published or filed as upstream issues.
