<!-- Research notes gathered on 2026-11-12 by a read-only research agent for PLAN.md. Statements marked [V] were read in the code; [I] are the agent's inferences and were not compiled. Line numbers refer to commit 81347267 and will drift. -->

# Research report: Aeneas proof tooling and itasca proof idioms

Paths are relative to the repository root. All paths below are relative to it. `AEN` = `lean/.lake/packages/aeneas` (pinned at `557eff83ecef5083b98a52a94ca7fae63d6c1dab`, Lean `v4.31.0`, confirmed in `lean/lake-manifest.json` and `lean/lean-toolchain`).

Nothing in the repo was modified. No lake/make/just/cargo was run. Scratch scripts lived in `$TMPDIR` and are deleted. Note: `git status` now shows an untracked `lean/scripts/` (Audit.lean, metrics.py, merge_modules.py, ...) created 13:14-13:17 today. That is not mine.

**Verified vs inferred.** Everything quoted is copied from files I read. Counts come from ripgrep or a regex-based theorem-block scan, so treat them as approximate (within a few percent). Items marked **[inferred]** are my reading, not something a file states.

Scope of handwritten proofs (`lean/Itasca/` minus `Generated/`): about 2,380 files, 340K lines, 9,570 theorems.

---

## Part A: Aeneas Lean library

### A1. The `step` tactic

Source: `AEN/backends/lean/Aeneas/Tactic/Step/Step.lean`. Docstring at lines 1192-1285, syntax at line 966, elaborators at 1286-1307. `step*` is in `AEN/backends/lean/Aeneas/Tactic/Step/StepStar.lean:846-887`.

Syntax (verbatim):
```lean
syntax stepArgs := Parser.Tactic.optConfig ("with" term)? ("as" " ⟨ " binderIdent,* " ⟩")? ("by" tacticSeq)?
elab (name := step) "step" args:stepArgs : tactic => do
elab tk:"step?" args:stepArgs : tactic => do
syntax (name := letStep) "let" noWs "*" " ⟨ " binderIdent,* " ⟩" colGe
  " ← " colGe ("[" Parser.Tactic.optConfig " ] ")? ("*?" <|> "*" <|> term) ("by" tacticSeq)? : tactic
syntax «step*_args» := (num)? Lean.Parser.Tactic.optConfig ("by" tacticSeq)?
syntax (name := stepStar) "step" noWs ("*" <|> "*?") «step*_args»: tactic
```

Variants:
- `step`, `step as ⟨ x, h1, h2 ⟩`, `step with thm`, `step with thm args as ⟨ ... ⟩`, `step ... by tac`.
- `step?` displays the theorem used and suggests `step with <thm>`.
- `step*` "repeatedly applies `step` and `split` on the goal"; `step*?` prints the equivalent script; `step* n` runs exactly n steps.
- `let* ⟨ z, h1 ⟩ ← *` is the alternative syntax.
- Options: `step +splitIte (splits := 6)`. See `Config` in `AEN/backends/lean/Aeneas/Tactic/Step/Init.lean:48-102`.
- Also `spec_split` / `spec_split as h` and `spec_split_if` (`StepStar.lean:93-149`).

What it does (docstring, verbatim): "looking for a suitable theorem (either provided by the user or looked up in the database of `step` theorems) which describes the behavior of a monadic function, then applying it to the current goal. It then introduces the existentially quantified variables and splits the conjunctions in the post-condition, before trying to solve the preconditions."

Docstring example:
```lean
h : 2 * (a.val + 1) < U32.max
⊢ (do
  let b ← a + 1#u32
  2 * b) ⦃ c => c > 0 ⦄
```
`step as ⟨ b ⟩` yields `b : U32`, `h_b : b.val = a.val + 1`, `⊢ 2 * b ⦃ c => c > 0 ⦄`.

Theorem lookup order (`stepAsmsOrLookupTheorem`, `Step.lean:884-964`):
1. The `with` argument if given.
2. Otherwise every local assumption, most recent first.
3. Otherwise the `@[step]` discrimination tree keyed on the function application, only if the head is a constant. The source says "we assume the most specific theorems are at the end" and tries them in reverse registration order.
4. Otherwise recursive `auxDecl` hypotheses, which is how a theorem applies itself.

On failure: `Step failed: could not find a local assumption or a theorem to apply`.

Preconditions:
- Defaults (`Init.lean:48-64`): `assumTac := true`, `inferGhostVars := true`, `grind := true`, `scalarTac := false`, `simpStar := false`. So `step` tries assumption matching, then `agrind` after scalar preprocessing, then the user's `by` tactic.
- Unsolved ones come back as goals ahead of the main goal: `setGoals (goals.unassignedVars.toList ++ sgs.toList ++ mainGoal)` (`Step.lean:1189`).
- The goal tag is the precondition's binder name in the spec. The test at `Step.lean:1392-1402` shows `case hmax`.

Naming without `as` (differs from the packaged markdown):
- Outputs take the bind variable names from the goal (`getVarNamesFromGoal`, `Step.lean:305-314`).
- Postconditions are named `<output>_post`, `<output>_post1`, ... (`Step.lean:552-605`). A test shows `z_post : ↑z = ↑x + ↑y`.
- `AEN/documentation/tactics-reference.md:21` says these get inaccessible names (`✝`). That is stale for this pin.
- Too many ids gives the warning `Too many ids provided`.

`progress` is still accepted, with a deprecation warning (`AEN/backends/lean/Aeneas/Tactic/Step/Deprecated.lean`): `progress`, `progress?`, `progress*`, `progress*?`, `@[progress]`, `@[progress_pure]`, `@[progress_pure_def]`. itasca uses none of them (0 `@[progress]`).

### A2. The `@[step]` attribute

Source: `Init.lean:171-353`. It takes no arguments (`Attribute.Builtin.ensureNoArgs`). `@[local step]`, `attribute [local step] thm` and `attribute [-step] thm` all work.

Required shape, from the comment at `Init.lean:206-211`:
```
∀ x1 ... xn, H1 → ... Hn → spec (f x1 ... xn) P
```
and from the tactic docstring:
```lean
theorem thm_name (arg1 : ty1) ... (argn : tyn)
    (h_pre1 : precondition_1) ... (h_prem : precondition_m) :
  f arg1 ... argn = ⦃ res1 ... resk => postcondition_1 ∧ ... ∧ postcondition_k ⦄
```
The `=` before `⦃` in that docstring is an upstream typo. Real syntax is `f args ⦃ r => P r ⦄`.

Details:
- The conclusion must be a fully applied registered spec predicate: `Std.WP.spec`, or `Std.WP.dspec` (the `⦄div` form) (`AEN/backends/lean/Aeneas/Tactic/Step/SpecInfo.lean`).
- `let` bindings in the statement are normalized away.
- Registration also generates a `<thm>.mvcgen_spec` lemma.
- Existential and conjunctive postconditions are supported. They are destructured in order into the `as ⟨...⟩` names: outputs first, then existential witnesses and conjuncts.
- Ghost variables (theorem arguments not in `f`'s arguments) are instantiated by matching preconditions against local assumptions.
- Related attributes: `@[step_pure pat]`, `@[step_pure_def]` (`Init.lean:819-1020`); simp sets `step_simps`, `step_pre_simps`, `step_post_simps`.

Upstream guidance on writing specs:
- Search for an existing spec first (`AEN/documentation/proof-strategies.md`).
- If `b` needs `a` to type-check, write `∃ (_ : a), b` instead of `a ∧ b` (`AEN/documentation/tips-and-tricks.md:180-189`).
- Watch truncated `Nat` subtraction in postconditions.
- Tag Rust constants `@[simp, scalar_tac_simps, agrind =, grind =, bvify]` so `step` discharges their side conditions.

### A3. WP notation `⦃ ... ⦄`

Source: `AEN/backends/lean/Aeneas/Std/WP.lean`.
```lean
@[expose] def Post α := (α -> Prop)
@[grind]
inductive spec {α} : (x : Result α) → (p : Post α) →  Prop where
| ret : ∀ {p x}, p x → spec (.ok x) p
```
Notation is scoped in namespace `Aeneas`, so files need `open Aeneas` (lines 266-267, 358-378):
```lean
scoped syntax:54 term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 term:55 " ⦃ " term " ⦄" : term
```
- `e ⦃ x => p ⦄` expands to `Aeneas.Std.WP.spec e (fun x => p)`.
- `e ⦃ p ⦄` takes a predicate directly. itasca uses this, e.g. `reader.read_f64_bits data start ⦃ FloatBits.Post 8 data start ⦄`.
- `⦃ x y => p ⦄` (separate binders) and `⦃ (x, y) => p ⦄` (tuple pattern) both destructure a pair result.
- `⦄div` is `dspec`, which also allows divergence.

Lemmas (verbatim statements):
```lean
@[simp, grind =, agrind =]
theorem spec_ok (x : α) : spec (ok x) p ↔ p x
@[simp, grind =, agrind =]
theorem spec_fail (e : Error) : spec (fail e) p ↔ False
@[simp, grind =, agrind =]
theorem spec_div : spec div p ↔ False
theorem spec_mono {α} {P₁ : Post α} {m : Result α} {P₀ : Post α} (h : spec m P₀):
  (∀ x, P₀ x → P₁ x) → spec m P₁
theorem spec_bind {α β} {k : α -> Result β} {Pₖ : Post β} {m : Result α} {Pₘ : Post α} :
  spec m Pₘ →
  (∀ x, Pₘ x → spec (k x) Pₖ) →
  spec (Std.bind m k) Pₖ
theorem spec_equiv_exists (m:Result α) (P:Post α) :
  spec m P ↔ (∃ y, m = ok y ∧ P y)
theorem spec_imp_exists {m:Result α} {P:Post α} :
  spec m P → (∃ y, m = ok y ∧ P y)
theorem exists_imp_spec {m:Result α} {P:Post α} :
  (∃ y, m = ok y ∧ P y) → spec m P
```
Also `spec_ok_pair`, `spec_dspec`, `dspec_mono`, `dspec_bind`, `dspec_ok`, `dspec_imp_forall`.

itasca usage counts: `spec_imp_exists` 1165 (362 files), `spec_mono` 1010, `WP.spec_ok` 1028, `spec_equiv_exists` 63, `exists_imp_spec` 16, `spec_bind` 13.

### A4. Arithmetic automation

| Tactic | Purpose | Source | itasca uses |
|---|---|---|---|
| `scalar_tac` | Preprocesses scalar bounds, then calls `omega`. Options `+split`, `+nonLin`. | `AEN/backends/lean/Aeneas/Tactic/Solver/ScalarTac/ScalarTac.lean:520-571` | 2020 in 561 files; `+nonLin` 0 |
| `simp_scalar` | "essentially equivalent to `simp (discharger := scalar_tac) [simp_bool_prop, simp_scalar_safe, simp_scalar]`"; simplifies `min a b`, `a % n`. Syntax `simp_scalar [lemmas] at h`. | `.../Tactic/Simp/SimpScalar/SimpScalar.lean:252` | 0 |
| `simp_lists` | Same principle for list get/set/append. | `.../Tactic/Simp/SimpLists/SimpLists.lean:86` | 0 |
| `bv_tac n` | `bvify n at *; simp_all only; bv_decide`, roughly. | `.../Tactic/Solver/BvTac/BvTac.lean:114` | 0 |
| `scalar_decr_tac` | `scalar_tac` for `decreasing_by`; clears Lean's termination clutter first. | `.../Tactic/Solver/ScalarDecrTac.lean:128` | 0 |

Also available: `bvify n`, `natify`, `zmodify`, `simp_ifs`, `split_conjs`, `fcongr`, `agrind`. itasca uses `agrind` 0 times and `grind` 8 times in 2 files.

Registration attributes, verified in the `Init.lean` files. The packaged markdown is stale here: it says `@[simp_scalar_simps]`, `@[simp_lists_simps]`, `@[bvify_simps]`. Those names do not exist in this pin.
- `@[scalar_tac_simps]`: simp lemma for `scalar_tac` preprocessing.
- `@[scalar_tac pat]`, `@[scalar_tac_nonlin pat]`: forward saturation rule with a trigger pattern. Example: `@[scalar_tac x.val] theorem UScalar.bounds ...`.
- `@[simp_scalar]`, `@[simp_scalar_safe]`.
- `@[simp_lists]`, `@[simp_lists_safe]`.
- `@[bvify]`, `@[natify]`, `@[zmodify]`, `@[simp_bool_prop]`, `@[simp_ifs]`.

itasca registers none of the scalar or list ones (0 matches for `@[...scalar_tac`). It has 86 `@[simp]` lemmas in 42 files.

### A5. Loops

Generated code (`lean/Itasca/Generated/Funs.lean`): 298 `@[rust_loop]` definitions, each paired with a `@[rust_loop_body]`. There are zero `partial_fixpoint`, `termination_by` or `decreasing_by` in Funs.lean, so no recursive `_loop` functions. Example, lines 21111-21131:
```lean
@[rust_loop_body]
def runtime.clear_loop.body
  {T : Type} (values : alloc.vec.Vec T) :
  Result (ControlFlow (alloc.vec.Vec T) (alloc.vec.Vec T))
  := do
  let b ← alloc.vec.Vec.is_empty Global values
  if b
  then ok (done values)
  else let (_, values1) ← alloc.vec.Vec.pop Global values
       ok (cont values1)

@[rust_loop]
def runtime.clear_loop
  {T : Type} (values : alloc.vec.Vec T) : Result (alloc.vec.Vec T) := do
  loop
    (fun values1 => runtime.clear_loop.body values1)
    values
```
Multi-variable state is a tuple: `loop (fun (params1, i1) => runtime.copy_type_loop0.body v params1 i1) (params, i)` (line 59664).

Library construct (`AEN/backends/lean/Aeneas/Std/Primitives.lean:464-474`):
```lean
inductive ControlFlow (α : Type u) (β : Type v) where
  | cont (v : α) -- continue
  | done (v : β) -- break
def loop {α : Type u} {β : Type v} (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  bind (body x) fun r =>
  match r with
  | ControlFlow.cont x => loop body x
  | ControlFlow.done x => ok x
partial_fixpoint
```

The library offers exactly two loop lemmas (`WP.lean:834-873`):
```lean
theorem loop.spec_decr_nat {α : Type u} {β : Type v}
  (measure : α → Nat)
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → Result (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄
```
`loop.spec` is the same with `(measure : α → γ) [wf : WellFoundedRelation γ]` and `wf.rel (measure x') (measure x)`.

Lean also auto-generates `loop.eq_def` and `loop.fixpoint_induct` from `partial_fixpoint`.

itasca usage:
- `loop.spec_decr_nat`: 201 uses in 161 files.
- Manual `rw [loop]` / `unfold loop`, usually under `Nat.strong_induction_on`, for inversion from `h : ..._loop ... = .ok r`: 116 uses in 69 files.
- `loop.fixpoint_induct` / `loop.eq_def`: 19 uses.

Project-local loop lemmas (not in `Support/`):
- `loop_trace_dspec` and `NormalTrace.result` in `lean/Itasca/Runtime/Interp/Control/LoopBasis.lean:15,24`.
- `loop_returned_invariant` in `lean/Itasca/Runtime/Platform/ReturnedLoop.lean:21`.
- `loop_erase` in `lean/Itasca/Runtime/Platform/Recording.lean:146`.

Upstream caveat (`tips-and-tricks.md:13-27`): upstream recommends `-loops-to-rec` because "the proof infrastructure for [the `loop` combinator] is less mature". itasca's Makefile (`lean/Makefile:56`) does not pass that flag, so itasca is on the combinator path.

### A6. Upstream docs and their advice

Files:
- `AEN/documentation/proof-strategies.md`, `tactics-reference.md`, `tips-and-tricks.md`, `getting-started.md`, `glossary.md`.
- `AEN/documentation/skills/aeneas-tactics-quickref.instructions.md`, `proof-patterns.instructions.md`, `aeneas-lean-core.instructions.md`.
- Tutorials: `AEN/tests/lean/Tutorial/{Tutorial,Exercises,Solutions}.lean`, `AEN/tests/lean/BaseTutorial.lean`.
- `AEN/docs/user/src/lean/tactics/step.md` is an empty stub.

Summary of the advice:
1. Standard shape: `@[step] theorem f_spec ... : f x ⦃ r => post r ⦄ := by unfold f; step*`, then one `·` block per remaining goal.
2. Workflow: `step*?` to generate a script, automate obligations, then refold to `step*`.
3. "Always write a separate theorem for each `_loop` function." Use three theorems per loop: a generalized `spec_gen`, a public `@[step] spec`, and a wrapper spec.
4. Never unfold standard library or auxiliary definitions mid-proof: "Unfolding is a sign that a lemma is missing."
5. Split large functions with helper definitions plus fold theorems: `simp only [helper, bind_assoc_eq, bind_tc_ok, pure]`.
6. "Avoid big `simp only [...]` in implementation proofs. The generated Rust model is unstable (names change on re-extraction)."
7. `simp_all` can delete needed hypotheses; prefer `simp [*]`.
8. Do not `exact` big anonymous-constructor terms; use `refine ⟨..., ?_, ?_⟩` and `·` blocks.
9. `maxHeartbeats` is "last resort only"; "If you need >1,000,000 heartbeats, the proof needs restructuring". Use the `set_option ... in` form per theorem. Target under 60s per proof.
10. Banned upstream: `omega`, `linarith`, `nlinarith`, `congr N`, `step* <;> tac`, `all_goals tac`, named `cases ... with | Foo =>` arms, `partial_fixpoint_induct`.

Upstream rules that itasca currently contradicts, which the guide must take a position on:
- `omega`: 4012 uses in 1011 files.
- `all_goals`: 1170 uses in 296 files.
- `cases r with | Err e => ... | Ok pair => ...` is the house idiom.
- `simp only` is the most common simp form (9078 uses).
- Loops are proven through the combinator.

---

## Part B: itasca handwritten proofs

Usage profile:
- `@[step]` on about 760 theorems in 236 files; `@[local step]` 20.
- `step with` 1341 (745 also have `as`); `step as ⟨` without `with` 1243; bare `step` 242; `step*` 230 in 77 files; `step ... by` about 37; `step?`, `step*?`, `let*` 0.
- So even `@[step]`-tagged specs are usually applied explicitly with `step with name args as ⟨...⟩`.

A second, equally common way to consume a spec is by rewriting:
```lean
obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (callee.spec args)
rw [hr]   -- or simp [caller, hr, ...]
```
The inversion direction uses `ResultFacts.bind_ok_inv _ _ _ h` (662 uses in 141 files).

### B1. Exemplary theorems

1. `lean/Itasca/Handler/Stack.lean:17-23`. Spec tagged, proof is `unfold` plus `step*`:
```lean
@[step]
theorem code.push_val.spec (st : code.OpIterState) (t : code.StackType)
    (hsize : st.vals.val.length < Usize.max) :
    code.push_val st t ⦃ st' =>
      st'.vals.val = st.vals.val ++ [t] ∧ st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  unfold code.push_val
  step*
```
Consumer: `lean/Itasca/Handler/ScalarConst.lean:23-31` (`code.read_i64_const.from_read`) ends with `step*` over a body that calls `code.push_val`. **[inferred]** that `step*` resolves it through this spec; I did not run it.

2. `lean/Itasca/Module/Readers/Basic.lean:82-89`. Iff postcondition, side goals closed by `scalar_tac`:
```lean
@[step]
theorem metadata.have_bytes.spec (data : Slice U8) (pos n : Usize)
    (hb : pos.val ≤ data.length) :
    metadata.have_bytes data pos n ⦃ r =>
      (r = .Ok () ↔ pos.val + n.val ≤ data.length) ∧
      (r = .Err .UnexpectedEof ↔ data.length < pos.val + n.val) ⦄ := by
  unfold metadata.have_bytes
  step* <;> scalar_tac
```

3. `lean/Itasca/Runtime/Store/Api/Grow.lean:7-14`, and its caller:
```lean
@[step] theorem within_spec (current additional limit : Usize) :
    runtime.store.within current additional limit ⦃ answer =>
      answer = decide (current.val + additional.val ≤ limit.val) ⦄ := by
  unfold runtime.store.within
  step as ⟨total, ht⟩
  cases total with
  | none => simp_all; scalar_tac
  | some total => simp_all
```
Caller, `lean/Itasca/Runtime/Store/Api/DefineMemory.lean:43-44,60-61`:
```lean
  unfold runtime.store.Store.define_memory_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  ...
        step with within_spec s.memory_bytes (Slice.len (view buffer)) s.limits.max_memory_bytes as ⟨fits, hfits⟩
        rw [hfits]
```

4. `lean/Itasca/Runtime/Interp/Simd/Relations/Slots.lean:18-28`. Consumes `get_effect` (`lean/Itasca/Runtime/Interp/Relations/Synthetic.lean:54`) and is itself consumed at `lean/Itasca/Runtime/Interp/Simd/Relations/OperandsBounded.lean:20` by `step with vector_effect slots position (space two) as ⟨value,bits⟩`:
```lean
@[step] theorem vector_effect (slots : Slice U64) (position : Usize)
    (space : position.val < Usize.max) :
    runtime.interp.vector slots position ⦃ value => value.bv = vectorBits slots.val position.val ⦄ := by
  unfold runtime.interp.vector
  step with get_effect as ⟨lo, hlo⟩
  simp only [lift, bind_ok]
  step as ⟨next, hnext⟩
  step with get_effect as ⟨hi, hhi⟩
  step as ⟨shifted, hshifted, shiftBits⟩
```

5. `lean/Itasca/Wasm2/Trace/ControlRecords.lean:30-36`. The caller steps through the callee's spec instead of unfolding it:
```lean
theorem code.call_indirect_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (profile : ValidationProfile) (hs : Control.Shape st.core) :
    code.call_indirect_info st data env profile ⦃ r => ∀ index table, r.1 = .Ok (index, table) →
      ∃ middle, Leb128.Decoded data st.core.pos index middle ∧
        Leb128.Decoded data middle table r.2.core.pos ⦄ := by
  unfold code.call_indirect_info
  step with code.take_index.spec st.core data as ⟨r, s, hv, hc, hd⟩
```

Also useful as templates:
- Loop spec: `lean/Itasca/Handler/Stack.lean:40-75`, `code.push_types_loop.spec`. Shape: `unfold code.push_types_loop`, `apply loop.spec_decr_nat (fun p => ts.val.length - p.2.val) (fun p => <invariant>)`, `· rintro ⟨s, j⟩ ⟨hij, hj, ...⟩; dsimp only at ...; unfold code.push_types_loop.body; split`, then `· exact ⟨...⟩` for the initial invariant.
- Wrapper delegating to a loop spec: `Stack.lean:78-84`, `simpa using code.push_types_loop.spec st ts 0#usize (by simp) (by simpa using hsize)`.
- Hypothesis-as-spec: `lean/Itasca/Runtime/Interp/Numeric/Float.lean:98-105`, `step with hf.f32_add a b as ⟨raw, hraw⟩`.
- Postcondition weakening: `lean/Itasca/Wasm2/References/ReadersTotal.lean:22-27`, `apply WP.spec_mono (code.take_index.spec st data)` then `rintro ⟨r, s⟩ ⟨hv, hc, hd⟩`.

### B2. Naming conventions

`@[step]` theorems, by suffix of the full name:

| Suffix | Count |
|---|---|
| `_total` | 95 |
| `.spec` | 92 |
| `_sound` | 82 |
| `_effect` | 49 |
| `.total` | 37 |
| `_spec` | 33 |
| `_loop` | 27 |
| `_bounded` | 20 |
| other (often named after the operation, e.g. `scalar_i64_add`, `enter_if`) | about 313 |

The split is by area:
- Validator layers (`Binary`, `Handler`, `Module`, `Stream`, `Wasm2`): 148 of 163 `@[step]` theorems hang off the Rust path, `code.push_val.spec`, `metadata.have_bytes.spec`, `code.take_index.total`. Sub-cases get a descriptive last component: `.above_base`, `.from_read`, `.eof`, `.complete`, `.wasm2`, `.reject`.
- `Runtime/`: all 596 `@[step]` theorems are bare snake_case inside `Itasca.Runtime.*` namespaces: `within_spec`, `room_spec`, `get_effect`, `binary32_add_sound`, `slots_fit_total`. Zero use the Rust path.

Across all 1,746 theorems with a `⦃ ⦄` conclusion (only 729 are tagged): `_total` 196, `_sound` 158, `.spec` 123, `_available` 116, `_effect` 100, `_spec` 68, `.total` 49.

Across all theorems by dotted last component: `.complete` 142, `.spec` 141, `.total` 61, `.sound` 19.

Existing written convention, `lean/PROOF_GUIDE.md:283-327`: "Facts about extracted functions hang off their Rust path, such as `metadata.validate_module.profile_sound` and `runtime.interp.invoke_with.behaves`." It also says suffixes `_eq`, `_iff`, `_sound`, `_complete`, `_spec` "are useful when they describe the conclusion; they are not required endings". The Runtime `@[step]` lemmas do not follow the Rust-path rule.

Meaning in practice **[inferred from reading about 20]**:
- `.spec`: the functional postcondition.
- `.total` / `_total`: returns normally, with shape or frame facts.
- `.complete`: the converse, an equation `f x = .ok (.Ok ..)` from a spec-side witness.
- `_sound`: result refines the SpecTec relation.
- `_effect`: state effect of a runtime helper.

### B3. Anti-patterns

**(a) Caller unfolds a callee that has a spec.** My automated match found about 120 hits, but only for callees named `F.spec` / `F.total`, so this undercounts Runtime.

1. `lean/Itasca/Runtime/Compiler/Body/Relations/Calls/IndirectCalls.lean:33-36` (repeated at 43 and 57). Specs exist: `code.take_index.spec` (`Handler/EnvReaders.lean:96`), `code.check_table_byte.spec` (`Wasm2/ProfileFilters.lean:71`), `code.call_indirect_info.total` (`Wasm2/Control/Total.lean:144`).
```lean
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
```
2. `lean/Itasca/Wasm2/Control/Call.lean:114-118`, `code.call.indirect_prefix`. Same shape: `simp [code.call, code.call_indirect_info, code.take_index, hr, ...]`. `code.take_index.spec` is in scope through `import Itasca.Handler.EnvCalls`. Contrast with B1 item 5.
3. `lean/Itasca/Runtime/Compiler/Body/Reader/Replay/OpcodeClassification.lean:77-78`. The equation `code.check_opcode.wasm2 : code.check_opcode .Wasm2 op = .ok (.Ok ())` exists at `Wasm2/ProfileFilters.lean:17`.
```lean
  unfold code.step_profile at accepted
  simp only [code.check_opcode, bind_ok, hok] at accepted
```
4. `lean/Itasca/Stream/FramingStep.lean:259-262`. `stream.read_exact.spec` exists at `Stream/Source.lean:81`, but it takes the fact being derived here as a premise, so this is a "spec too weak for the inverse direction" case.
```lean
    obtain ⟨r, hread, _⟩ := ResultFacts.bind_ok_inv _ _ _ hr
    unfold stream.read_exact at hread
    obtain ⟨r, hsource, _⟩ := ResultFacts.bind_ok_inv _ _ _ hread
    exact ⟨r, hsource⟩
```
5. `lean/Itasca/Wasm2/References/Complete.lean:209-211`, `Frame.ref_func`. `code.read_ref_func.total` is `@[step]` at `Wasm2/References/ReadersTotal.lean:110`.
```lean
  have hrun : code.read_ref_func st.core data env = .ok (.Ok idx, s) := by
    simp [code.read_ref_func, hread, lift, Nat.not_le_of_gt hi, metadata.Env.declares_function.eq,
      himem, hs, core.result.Result.Insts.CoreOpsTry.branch]
```

Other instances: `lean/Itasca/Runtime/Compiler/Body/Reader/Control/BranchTableSourceBoundAcceptance.lean:482,565` (`unfold code.branch_table_with`, spec at `Wasm2/Visitor/Total.lean:140`); `lean/Itasca/Runtime/Compiler/Body/Reader/Control/BranchInfo.lean:54`.

Caveat for the guide: many of these need an exact equation (`f x = .ok v`), which a `.total` spec does not give. The fix is usually a missing equation or `.complete` lemma, not `step`.

Related brittleness: 274 uses in 50 files of `with_unfolding_all change (<whole restated body>) ⦃ ... ⦄` after `unfold`, e.g. `lean/Itasca/Runtime/Interp/Numeric/Float.lean:103`. It restates the dispatcher arm by hand.

**(b) Non-terminal bare `simp` / `simp at h` / `simp_all`.** 147 occurrences in 64 files (79 `simp`, 61 `simp at`, 7 `simp_all`). Worst files: `Stream/DriverRun.lean` 12, `Stream/InvariantDriver.lean` 10, `Stream/DriverTotal.lean` 10. Context: `simp only` 9078, `simp [` 5795, `simpa` 7987, `simp_all` 705.

1. `lean/Itasca/Stream/DriverRun.lean:130`
```lean
                  | Ok moduleEnd =>
                    simp at h
                    obtain ⟨region, hregion, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                    obtain ⟨⟨r, decoded⟩, hdecoded, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
```
2. `lean/Itasca/Module/Code/Entry.lean:102`
```lean
            have hbytes := hhpost.1.mp rfl
            simp
            step
            obtain ⟨r, hl, hlpost⟩ := WP.spec_imp_exists (metadata.decode_locals.spec data content profile)
```
3. `lean/Itasca/Wasm2/Control/Frame.lean:162-164`
```lean
    simp [code.read_multi_value_label, hr, core.result.Result.Insts.CoreOpsTry.branch]
    simp_all
    exact ⟨depth, hl⟩
```
4. `lean/Itasca/Stream/FramingTotal.lean:177`
```lean
                  | Ok finish =>
                    simp
                    split
                    · simp [StreamFraming.BatchPost]
```
5. `lean/Itasca/Runtime/Store/Invariant/InternTypeCauses.lean:58`
```lean
          · simp
            step with copy_type_resource_causes allocator law ty as ⟨copied,effect⟩
            rcases effect with copiedEq | ⟨failed,refusal⟩
```

Also `lean/Itasca/Stream/SubmissionSound.lean:302` and `lean/Itasca/Runtime/SourceMachine/Bound.lean:201` (`simp at hh ⊢` then `omega`).

**(c) `all_goals try` / `first |` case-bashing.** `all_goals` 1170 (296 files); `all_goals try` 182 (83 files); `first |` 1091 (234 files); `repeat` 787; `<;> try` 94.

1. `lean/Itasca/Binary/Wasm1/MemoryTyping.lean:112-121`
```lean
  split at h <;> cases h
  all_goals first
    | exact fullLoad_typed _ _ _ 32 rfl rfl (by norm_num)
    | exact fullLoad_typed _ _ _ 64 rfl rfl (by norm_num)
    | exact fullStore_typed _ _ _ 32 rfl rfl (by norm_num)
    | exact fullStore_typed _ _ _ 64 rfl rfl (by norm_num)
    | apply packedLoad_typed
    | apply packedStore_typed
  all_goals try (apply wf_sz.sz_case_0; norm_num)
```
2. `lean/Itasca/Visitor/Total.lean:376-...`, one alternative per opcode:
```lean
  unfold code.visit_memory
  split <;> first
  | exact h.on_i32_load v st memarg
  | exact h.on_i64_load v st memarg
  | exact h.on_f32_load v st memarg
```
3. `lean/Itasca/Wasm2/Control/EndTotal.lean:128-133`
```lean
      repeat' first
        | contradiction
        | rfl
        | simp_all [Std.uncurry, Std.bind_assoc]
        | (congr 1; funext x)
        | split
```
4. `lean/Itasca/Runtime/Interp/Numeric/Float/FloatDispatch.lean:24-...`
```lean
    cases ty <;> cases operation
    all_goals first
      | exact scalar_f32_abs_instruction ops a b
      | exact scalar_f32_neg_instruction ops a b
      | exact scalar_f32_ceil_instruction ops correct a b
```
5. `lean/Itasca/Runtime/SourceMachine/Stateful/Ownership.lean:308-310` (15 `all_goals try` in this file)
```lean
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,as_reference_value]
    all_goals
      apply stateful_owned_advance (step := step)
```

Also `lean/Itasca/Wasm2/References/ReadersTotal.lean:129-131`: `step*`, then `all_goals try (rcases val with ⟨index, ty⟩)`, then `all_goals step*`.

**(d) `set_option maxHeartbeats N`, N ≥ 2,000,000, not scoped with `in`.** 172 occurrences in 153 files: 8,000,000 ×6, 4,000,000 ×41, 3,000,000 ×7, 2,000,000 ×118. For comparison there are 56 `set_option maxHeartbeats N in` uses (25 of them ≥ 2M), and 289 unscoped `maxRecDepth`. In consolidated files the option sits inside a section's namespace block, so it is scoped to that block rather than the whole file (see B5).

1. `lean/Itasca/Runtime/Compiler/Local/Relations/Syntax/ReaderOpcode.lean:12-15`
```lean
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open Aeneas Aeneas.Std Itasca
namespace Itasca.Runtime.Compiler
```
2. `lean/Itasca/Runtime/Compiler/Body/Reader/Replay/OpcodeClassification.lean:12-17`
```lean
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
```
3. `lean/Itasca/Runtime/Compiler/Local/Callbacks/Control/FixupBranchPreservation.lean:2-5`
```lean
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
```
4. `lean/Itasca/Runtime/Interp/Simd/Execution/PureSound.lean:15-18`: `set_option maxRecDepth 4096` / `set_option maxHeartbeats 4000000` after `namespace` and `open`.
5. `lean/Itasca/Runtime/Compiler/Module/WellFormedTotal.lean:15-16` and again at `51-52`: the same pair repeated in two of its three sections.

Others at 8M: `lean/Itasca/Runtime/Compiler/Local/Capacity/SimdOpAvailability.lean:20`, `lean/Itasca/Runtime/Compiler/Body/Reader/Source/SourceOpcodeDescriptors.lean:10`, `lean/Itasca/Runtime/Compiler/Body/Reader/Safety/ScalarDispatchSafety.lean:14`.

The per-theorem form in use: `set_option maxHeartbeats 1200000 in` placed directly above the docstring (`lean/Itasca/Binary/Wasm1/PrefixUnique.lean:34`).

**(e) Theorems with more than about 25 binders.** I counted binder names in the signature, which includes data parameters and type variables as well as hypotheses. I could not separate hypotheses syntactically. Distribution: 16-25: 941 theorems; 26-30: 188; 31-40: 175; 41-50: 48; over 50: 11. So 422 theorems exceed 25. The codebase also has 78 `structure ... : Prop where` bundles in 66 files, which is the existing remedy.

1. `lean/Itasca/Runtime/Integration/Host/HostIndirectSelectedWorld.lean:9`, `call_indirect_host_structured_world`, 64 binders, 143 lines:
```lean
theorem call_indirect_host_structured_world {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
```
2. `lean/Itasca/Runtime/Interp/Machine/Calls/IndirectSelected.lean:20`, `call_indirect_selected`, 59 binders. By my manual count about 21 are propositional hypotheses, from `(allocation : Platform.AllocCorrect allocator)` through `(machine : Execution view code store exec ⟨...⟩ expected raw.pc.val false)`.
3. `lean/Itasca/Runtime/Spec/Instantiation.lean:37`, `instantiate_source`, 58 binders:
```lean
theorem instantiate_source
    (s after : store) (source : module) (externals : List externaddr)
    (types : List functype) (imports : List «import») (functions : List func)
    (globals : List global) (tables : List table) (memories : List mem)
```
4. `lean/Itasca/Runtime/Interp/Machine/Simd/MemoryFrame.lean:23`, `step_memory_frame`, 56 binders.
5. `lean/Itasca/Runtime/Store/Preparation/StagingCommitShape.lean:330`, `staging_commit_shape`, 54 binders.

Next largest: `step_indirect_host_world_outcomes` (57, `lean/Itasca/Runtime/Integration/Host/HostIndirectWorld.lean:8`), `step_host_call_structured_world_provenance` (53, `lean/Itasca/Runtime/Integration/Host/HostCallStructuredWorld.lean:15`).

### B4. `lean/Itasca/Support/` (6 files, 546 lines)

There are no tactics, no `@[step]` theorems and no loop lemmas here.

- `Result.lean` (22 lines), namespace `Itasca.ResultFacts`. One lemma:
```lean
theorem bind_ok_inv {A B : Type} (read : Result A) (next : A → Result B) (b : B)
    (h : (read >>= next) = .ok b) :
    ∃ a, read = .ok a ∧ next a = .ok b
```
Used as `obtain ⟨a, ha, h⟩ := ResultFacts.bind_ok_inv _ _ _ h` (662 uses; 154 files `open ... ResultFacts`). A private duplicate exists: `returned_bind` in `lean/Itasca/Runtime/Platform/ReturnedLoop.lean:10`.

- `LiteralDispatch.lean` (52 lines). `meta def reduceLiteralDispatch (opcodePos : Nat) : Simp.Simproc` reduces a dispatcher when its opcode argument is a concrete scalar literal, with proof by `mkEqRefl`. Simprocs:
  - `reduceConvertTypes (Itasca.code.convert_types _)`
  - `reduceBinaryTypes (Itasca.code.binary_types _)`
  - `reduceVisitNumeric (Itasca.code.visit_numeric _ _ _ _)`
  - `reduceVisitMemory (Itasca.code.visit_memory _ _ _ _ _)`
  - `reduceStepMemory (Itasca.code.step_memory _ _ _ _ _ _)`
  - `reduceStep (Itasca.code.step _ _ _ _ _ _ _)`
  - `reduceScalarMatcher (_)`, for any single-discriminant match on a `UScalar` literal.

  They are declared `simproc ↓`, so they are on by default in `simp`.

- `BodyState.lean` (69 lines). `def code.BodyState.blocks` projects the control stack. `@[simp]` lemmas: `blocks_val`, `blocks_length`, `blocks_len`, `blocks_is_empty`, `blocks_eq_iff`, `blocks_pos`, `blocks_vals`. Non-simp: `blocks_index`, `blocks_eq_of_ctrls`. Also `limits.MAX_FUNCTION_BYTES.room : limits.MAX_FUNCTION_BYTES.val + 2 < Usize.max`.

- `TypeTranslation.lean` (56 lines), namespace `Itasca.Translate`. Defs `valueType`, `referenceType`, `mutability`, `globalType` (Rust type to SpecTec type). Lemmas `valueType_injective`, `mutability_injective`, `valueType_eq` (extracted `PartialEq` agrees with `decide`), `globalType_valid`.

- `EnvTranslation.lean` (292 lines), namespace `Itasca.EnvTranslation`.
  - Defs: `funcType`, `limitsType`, `tableType`, `memType`, `elementTypes`, `dataTypes`, `context`.
  - Well-formedness: `index_wf`, `limitsType_wf`, `tableType_wf`, `memType_wf`, `context_wf`.
  - `structure Matches env ctx C : Prop` with `Matches.root`, `.wf`, `.local`, `.global`.
  - `Matches.local_get/local_set/local_tee/global_get/global_set/call/call_indirect/memory_size/memory_grow` turn env bounds into `Instr_ok` premises.
  - Lookups: `.local_lookup`, `.global_lookup`, `.func_lookup`, `.type_lookup`, `.table_lookup`, `.table_funcref`, `.memory_exists`.

- `ControlTranslation.lean` (55 lines). `Control.labelContext`, `labelContext_labels` (`@[simp]`), `labelContext_wf`, `enter_context_wf`, `EnvTranslation.Matches.enter`, `Wasm2.blockType`, `Wasm2.blockType_wf`.

Shared helpers outside `Support/`: the loop lemmas listed in A5, and `lean/Itasca/Runtime/Representation/Collection.lean` (slice lookup and list transport, per `lean/Itasca/Runtime/README.md:353`).

### B5. Module docstrings and section structure

There are two conventions, split by area.

Validator layers (400 files): 391 start with a module docstring after the imports, and 379 of those use a `# Title` heading. Then `open Aeneas Aeneas.Std` and one `namespace Itasca ... end Itasca`. Example, `lean/Itasca/Handler/Stack.lean:3-14`:
```lean
/-!
# Operand stack primitives

Specifications of the extracted stack helpers used by every instruction handler: ...
-/

open Aeneas Aeneas.Std

namespace Itasca
```

Runtime (1,979 files):
- 988 have a leading docstring and 991 have none (e.g. `lean/Itasca/Runtime/Store/Api/Grow.lean`).
- The docstring is prose with no `#` title.
- 533 files carry this trailer: `Main declarations: \`a\` and \`b\`. A direct consumer is \`Module.Path\`.`

Consolidated files: 323 files, all under `Runtime/`, with 920 sections in total. The pattern is uniform. Skeleton from `lean/Itasca/Runtime/Integration/Invocation/Behaves.lean:8-67`:
```lean
/-!
Public invocation behavior, termination recovery and exclusion of spurious errors. ...
-/

/-! ## Public Executable World Divergence -/

section

/-! Public evolving-world divergence reflection and normal-return recovery.
Lookup evidence is shared with terminal correspondence; source productivity remains separate. -/
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- ... -/
theorem invoke_executable_world_infinite_source {M P F A : Type}
  ...
end Itasca.Runtime.Integration

end
```
Precisely:
- One file-level `/-! ... -/` docstring after the imports.
- Each former file becomes: a `/-! ## Title Case Name -/` header (919 of 920 sections), a blank line, an anonymous `section`, optionally the former file's own `/-! ... -/` docstring, its own `namespace X` (919 of 920), its own `open ...` (896 of 920), the declarations, `end X`, then a bare `end`.
- No consolidated file has `namespace`, `open` or `set_option` outside its sections.
- `set_option`: kept per section, right after that section's `namespace` and `open` (109 sections). It therefore applies only to that block. Example: `lean/Itasca/Runtime/Compiler/Module/WellFormedTotal.lean` repeats `set_option maxRecDepth 4096` / `set_option maxHeartbeats 4000000` in sections 1 and 2 (lines 15-16, 51-52), and section 3 (line 117 on) runs at defaults. **[inferred]** that this scoping follows from Lean's rule that options end with the enclosing `namespace`/`section`; I did not test it.
- `private`: left as `private` inside its section (43 sections have private declarations), e.g. `lean/Itasca/Runtime/Interp/Memory/MemoryDecode.lean:30,67,91`. **[inferred]** `private` in Lean is file-scoped, not section-scoped, so these names are visible to later sections and two sections cannot reuse a private name in the same namespace. I saw no renaming scheme for collisions.
- Local attributes, notations and macros inside sections are rare (3 sections), e.g. `local macro "simd_constructor_case "` in `lean/Itasca/Runtime/Compiler/Local/Lowering/Simd/SimdConstructor.lean:14`.

Written rule already in the repo (`lean/PROOF_GUIDE.md:313-316`, repeated in `lean/Itasca/Runtime/README.md:332-337`): "Begin each new or consolidated module with a docstring explaining its question, main relation or result, and consumers; use section comments to mark argument stages."

### B6. Auto-generated names

Inaccessible names are essentially absent: `✝` 0 matches, `a✝` 0. The dependence on generated names takes other forms.

1. Aeneas binder names from `Funs.lean`, picked up by `step*` or bare `step` (155 `*_post` references in 44 files; most frequent `v1_post`, `v_post`, `r_post`, `out1_post`, `b_post`, `i2_post`).
   - `lean/Itasca/Binary/ReadByte.lean:22-24`. `b` and `i1` come from `let b ← Slice.index_usize data pos` and `let i1 ← pos + 1#usize` at `Funs.lean:1194-1195`:
   ```lean
     unfold reader.read_byte
     step*
     exact ⟨i1, by rw [b_post], i1_post⟩
   ```
   - `lean/Itasca/Handler/Stack.lean:67-72`: three bare `step`, then `rw [st1_post, i2_post, vt_post, ← hv]`. Same in `lean/Itasca/Module/Readers/Copies.lean:45`: `rw [out1_post, i2_post, vt_post, ← hv]`.
   - `lean/Itasca/Wasm2/References/ReadersTotal.lean:130,171`: `all_goals try (rcases val with ⟨index, ty⟩)` and `rcases val1 with ⟨index1, ty1⟩`. `val` is the generated `ControlFlow.Continue val` binder.

2. `split`-generated case tags that depend on match arm order in `Funs.lean` (`case h_N` in about 10 files).
   - `lean/Itasca/Wasm2/Visitor/Step.lean:42-43`:
   ```lean
     split at h
     case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_10 | h_11 =>
   ```
   - `lean/Itasca/Wasm2/Trace/BytesBulk.lean:229-254`: `split at run` then `case h_1 =>` through `case h_10 =>`, one per bulk opcode. Same in `lean/Itasca/Wasm2/Bulk/Visitor.lean:35-45` and `lean/Itasca/Wasm2/Trace/Refinement.lean:52-62`.

3. `rename_i` after `split` / `by_cases`: 871 uses in 320 files, e.g. `lean/Itasca/Handler/Stack.lean:59-60`, `split` then `· rename_i hstop`. This is positional in the unnamed hypotheses.

4. `this`: 203 uses in 166 files, mostly `have := ...` followed by `omega` or `simpa using this`. That is low-risk.

By contrast, `step as ⟨...⟩` and `step with ... as ⟨...⟩` with explicit names are the majority form (about 2,000 of roughly 2,800 `step` calls), so the explicit-naming style is already dominant.
