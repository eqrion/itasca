# Proof engineering guide

How to write and change proofs in this repository so they stay cheap to maintain
as the Rust code evolves. Read this before editing anything under `lean/Itasca/`
or `lean/SpecExt/`. [AGENTS.md](../AGENTS.md) holds the mandatory rules and
required checks; this guide explains how to do the work well. Where they
disagree, AGENTS.md wins.

The pinned Aeneas package ships its own proof documentation. Read it for tactic
details and worked examples; this guide does not repeat it:

- `.lake/packages/aeneas/documentation/skills/aeneas-lean-core.instructions.md`:
  the translation model, the specification pattern, pitfalls.
- `.lake/packages/aeneas/documentation/skills/aeneas-tactics-quickref.instructions.md`:
  which tactic to use for which goal.
- `.lake/packages/aeneas/documentation/proof-strategies.md` and
  `tips-and-tricks.md`: loops, function decomposition, proof time budgets.
- `.lake/packages/aeneas/documentation/skills/lean-lsp-mcp.instructions.md`:
  the language server tools and how to work with them.

Two project rules override that documentation: never use `native_decide`,
`sorry` or new axioms; and `omega` and named `cases ... with | Ctor =>` arms are
allowed as described in rule 6. The Markdown files lag the code in
places (for example attribute names such as `@[simp_scalar_simps]` do not exist
at this pin). When they disagree with the Lean sources under
`.lake/packages/aeneas/backends/lean/Aeneas/`, the sources are right.

## Use the language server

Proof work in this repository expects the Lean language server tools
(`lean-lsp-mcp`). They show the goal at any position, report errors for one
file without a build, and try several tactics without editing the file. A
`just check` cycle costs seconds to minutes and shows no intermediate goals.

- Iterate with the tools: `lean_goal` to see the proof state,
  `lean_diagnostic_messages` after an edit, `lean_multi_attempt` to compare
  candidate tactics before writing one.
- If the tools are not available to you, say so to the user before starting
  proof work. `just check` is the fallback, not the default.
- The server elaborates the current file against compiled imports. Reuse the
  existing cache. If imports are missing or stale, run `just check` on the
  needed dependency or target before querying it. A full build is not a
  prerequisite for every editing session. After editing an imported module,
  check the dependents you are about to open so they use its current version.
- Never run `lake clean` or delete `lean/.lake/`.
- The first answer for a file costs its elaboration time. Most files take
  seconds; a few take several minutes. Consult existing build traces before
  deciding that another check or profile is useful.
- Finish with the commands under "Before you finish". The language server does
  not replace the full build.

Configure `lean-lsp-mcp` through the editor or agent's MCP configuration.
The project root is `lean/`. If discovery fails, set `LEAN_PROJECT_PATH` to that
absolute directory in the server environment.

## Why these rules exist

A proof base dies when a small Rust change breaks proofs all over the tree.
What decides the cost of a change is how many proofs can see the thing that
changed. Every rule below reduces that number or makes it measurable.

There are three kinds of Lean text here, with different standards:

| Kind | What it is | Standard |
| --- | --- | --- |
| Statements | All public theorems in `Itasca/Results/` and their transitive semantic vocabulary in `Itasca/Results/Definitions/`, plus named foundations. | A human reads these; document their exact meaning. Changes to types, bodies or premises can change what is claimed. |
| Contracts | One specification theorem per extracted Rust function. | The only place that looks inside that function. Stable interface for every other proof. |
| Proofs | Everything else. | Lean checks them. Optimize for robustness and build time, and delete what is unused. |

The [definition reading map](Itasca/Results/Definitions/README.md) and generated declaration
index separate statement meaning from construction. Source ownership is
independent of namespace prefixes. Public vocabulary placement
overrides the rule that implementation proof files mirror Rust. Do not import
implementation proofs into public definitions to avoid exposing a large certificate.
Move its semantic components faithfully; Support contains only prerequisites
needed to elaborate definitions. The one-contract-per-function rule below is
an implementation discipline, not a separate public contract entry point.

## Names and ownership

A namespace identifies a semantic subject; a module identifies its dependency
owner. Follow [NAMESPACES.md](NAMESPACES.md): use subjects such as `Itasca.Compiler`,
`Itasca.Representation` and `Itasca.Stream.Batch` in both definitions and proofs.
Definitions, Results and Runtime are organizational directories and do not add
namespace prefixes. Files group related arguments or dependency stages, and their
introductions describe the complete group. Extracted/upstream operation contracts
retain the actual operation namespace; public runtime wrappers use semantic API
subjects where an internal contract already occupies that identity.

Types, certificates and named semantic predicates use `UpperCamelCase`.
Computations use `lowerCamelCase`; extracted and upstream names keep their
original spelling. Theorem basenames use `lower_snake_case`, including facts
about a computation: `body_type_root`, not `bodyType_root`. Constructors and
structure fields follow their owning type's conventions; a theorem rename must
not rename a coincidentally spelled constructor or field.

An extracted function contract is `<function>.spec`. Use `.total` for normal
return, `.sound` for acceptance correctness, `.complete` for acceptance from
independent premises, `.preserves_*` for retained invariants and `.unique` for
uniqueness. Name hypotheses after facts such as `encoded`, `typed`, `reachable`
and `allocator_correct`. Distinguish language restrictions from implementation
limits and success from normal return.

Qualifiers must name real distinctions. Body validation and code entries are
shared subjects; scalar proofs are an internal decomposition, not a language
mode. Keep the exact extracted `step_wasm2` and `step_profile` names at the Rust
boundary. Avoid adding aliases for identical predicates merely to match a proof
stage or filename.

## Rules

### 1. One contract per extracted function

Every function in the generated `Itasca/Generated/Funs*.lean` partitions that
proofs reason about has
exactly one specification theorem, named `<function>.spec`, tagged `@[step]`,
stated with the postcondition notation:

```lean
/-- **Spec theorem for `itasca::code::push_val`**
Pushes one operand type and leaves the control stack and cursor alone. -/
@[step]
theorem code.push_val.spec (st : code.OpIterState) (t : code.StackType)
    (hsize : st.vals.val.length < Usize.max) :
    code.push_val st t ⦃ st' =>
      st'.vals.val = st.vals.val ++ [t] ∧ st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  unfold code.push_val
  step*
```

That one is real ([Handler/StackEffects.lean](Itasca/Handler/StackEffects.lean)). A function
that can fail and that changes a larger state has this shape (schematic; the
effect relations are yours to define, see rule 2):

```lean
@[step]
theorem runtime.compiler.FunctionCompiler.emit.spec {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (self : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) :
    runtime.compiler.FunctionCompiler.emit ops self instruction ⦃ (result, after) =>
      match result with
      | .Ok () => EmitEffect self instruction after
      | .Err error => EmitRefused self error after ⦄ := by
  unfold runtime.compiler.FunctionCompiler.emit
  ...
```

- Name the contract after the extracted function's full name plus `.spec`.
  Older runtime lemmas named `within_spec`, `get_effect` or `x_total` predate
  this rule; rename them when you touch them.

- The contract is the only theorem allowed to `unfold` the function or put it
  in a `simp`, `rw` or `delta` list. Every other proof reaches the function
  with `step`, `step with <function>.spec`, or by applying the contract.
- When a caller needs a fact the contract does not give, strengthen the
  contract. Do not unfold the function in the caller.
- When a proof has a hypothesis `called : f args = .ok result` and needs facts
  about `result`, apply the contract to it. Do not unfold `f`:

  ```lean
  have post := f.spec args
  rw [called, WP.spec_ok] at post
  ```

- When a proof needs the equation `f args = .ok value` itself, the contract's
  postcondition must determine the result (`result = g args`, or an effect
  relation that is functional). If it does not, strengthen the contract.
- `python3 scripts/metrics.py --top` lists the functions that break this rule
  most. The metric `extra_unfold_files` must never go up.

### 2. A contract describes the effect once; properties are derived from it

State what the function returns and how the state after relates to the state
before, completely enough that no caller needs the body. Then prove each
property (bounds kept, coordinates ordered, capacity respected) as a lemma
about the effect description, with no reference to the extracted function.

- Put the effect in a named structure or relation (`EmitEffect before
  instruction after`) with documented fields, one field per changed component,
  plus an explicit statement of what is unchanged.
- Use an exhaustive `match` on the Rust result, never a conjunction of
  implications. Cover the error cases: say whether the state is unchanged.
- Destructure tuples in the binder (`⦃ (result, after) => ... ⦄`). Never write
  `out.2.2.1`.
- Preconditions are hypotheses of the contract. Keep only the ones the
  function needs to return normally and satisfy its effect.
- A property that only holds together with an invariant is a lemma of the form
  `Invariant before → Effect before after → Invariant after`. It mentions no
  extracted function, so it survives any change that keeps the effect.

### 3. Large functions are decomposed, not attacked with bigger budgets

If a contract proof needs more than about 25 `step`s or more than 60 seconds,
split the function body with helper definitions and fold theorems, as described
under "Splitting Large Functions" in the Aeneas `proof-strategies.md`. Prove a
contract for each helper. For dispatch functions with hundreds of arms (for
example `lower.FunctionCompiler.op`), prove one contract per arm family and
state the top-level contract as a table over those families.

### 4. Proof files mirror Rust files

- One Lean module per Rust function or per small group of related functions,
  placed in a directory that mirrors `src/`. A reader holding `control.rs`
  should find its contracts by name.
- Order inside a module: effect definitions, the contract, derived properties.
- Group related contracts into substantial modules, with named sections for
  their component subjects. Import and startup time can cost several seconds
  before any proof is checked, so do not create a module for one short lemma.
  Use measured build time and dependency costs to choose boundaries: merging
  serial neighbors saves startup work, while merging independent branches can
  reduce parallelism or add expensive imports. Larger modules are appropriate
  when they remain coherent and shorten the clean build. Modules under 50 lines need a reason,
  such as a definition that must sit below its consumers. A short public-definition
  module is justified when it isolates a dependency
  needed to elaborate a public definition from its implementation proof. Such
  files remain visible in the raw `modules_under_50_lines` metric; only exact
  paths with a specific split reason in `metrics/short-module-ledger.json`
  are excluded from that metric's ratchet. Each path must also occur in the
  migration provenance manifest. Directory or pattern exemptions are forbidden;
  all other ratchets retain their existing thresholds.
- Start each module with a `/-! ... -/` docstring: the question it answers, its
  main declarations, and who uses them.
- When several former modules share one file, each gets a `/-! ## Name -/`
  heading followed by its own `section ... end` holding its `namespace`, `open`
  and any options, so nothing leaks into the next section. `private` names are
  shared by the whole file, so they must be unique within it.
- Select consolidation groups by their dependency graph and measured build cost,
  not line counts alone. Check for cycles, increased import depth, and additional
  transitive imports for existing consumers. Merging a foundational helper with
  a downstream proof can make every helper consumer load that proof's dependencies.
  Prefer related short chains or siblings with similar imports; keep expensive
  proofs separate so they can build in parallel. Compare clean project builds
  with dependency caches preserved, and retain the previous project cache.
- Import the lowest module that provides what you need. Follow the layering in
  [README.md](README.md#proof-architecture); `just lint` checks it.

### 5. Keep statements small

- At most about 12 hypotheses. When a theorem needs more, the hypotheses
  usually describe one situation: bundle them into a structure with named,
  documented fields and pass the structure. Proof size grows faster than
  statement size, so this pays twice.
- Name every hypothesis for what it says (`issued`, `bounded`), not `h1`.
- Do not introduce a new variant of an existing predicate by adding a
  qualifier (`Core`, `Supported`, `Cumulative`, `Eventful`). Extend the existing
  predicate, or replace it and migrate its users in the same change.
- New definitions that a headline theorem mentions go into the statement cone.
  Check `metrics/audit.txt` and say so in the change description.

### 6. Write proofs that survive re-extraction

The extraction pipeline regenerates the generated `Funs*.lean` partitions and
their `Funs.lean` umbrella whenever Rust changes. Bound variable names,
the order of binds and helper names can all change.

- Never refer to names Lean or Aeneas invented. That means the `i1`, `v2_post`
  names a bare `step` or `step*` takes from `Funs.lean`, the `h_3` case tags
  that `split` derives from match-arm order, and hypotheses picked up
  positionally by `rename_i`. Name what `step` introduces
  (`step as ⟨after, effect⟩`), and split on a named discriminant
  (`cases kind : function.code with | Wasm i f => ... | Host id => ...`).
- No non-terminal bare `simp`, `simp at h` or `simp_all`. A bare `simp` may
  only close a goal. Otherwise use `simp only [...]`, a named rewrite, or
  `simp [*]` followed immediately by a closing tactic.
- In lemmas about stable definitions (specification, effect relations), prefer
  `simp only [...]`. In contract proofs over extracted code, prefer `step` and
  registered lemmas over long `simp only` lists of generated names.
- Do not case-bash large enumerations with `cases x <;> ...`, `all_goals try
  ...` or long `first | ... | ...` chains. For `runtime.bytecode.Instr` (432
  constructors) use the classifier functions and the equation lemmas from
  `Itasca.Runtime.Equations.Bytecode`; interpreter equations are in
  `Itasca.Runtime.Equations.Interp`. Prove one lemma per instruction family.
  `all_goals` is acceptable only when one terminal tactic closes every goal.
- Arithmetic: use `scalar_tac` (or `agrind`) whenever the goal or a needed
  hypothesis mentions a Rust integer type or the length of a `Vec` or `Slice`.
  `omega` is fine for goals purely about `Nat` and `Int`.
- Extract a hard arithmetic or list fact into its own lemma with a small
  context instead of proving it inline in the middle of a contract.

### 7. Resource limits are a symptom

- No file-scoped `set_option maxHeartbeats` or `maxRecDepth` in new code. If one
  theorem needs a higher limit, write `set_option maxHeartbeats N in` directly
  above it with a comment that says why.
- Needing more than 1,000,000 heartbeats means the proof must be decomposed
  (rule 3). Never raise an existing limit to make a broken proof pass.
- The metrics `heartbeat_overrides` and `recdepth_overrides` must never go up.

### 8. Delete, do not accumulate

- Remove lemmas, definitions and files that nothing uses. Do not keep the old
  form of a theorem next to the new one.
- When a contract changes, update its callers in the same change. No
  compatibility aliases.
- Do not add a second proof path for something already proved. Search first:
  `rg "theorem .*<function>" Itasca`.

### 9. Protect the trust boundary

- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or
  `opaque` placeholders.
- Never edit `Itasca/Generated/Types.lean`, generated `Itasca/Generated/Funs*.lean`
  files, or `SpecTec/wasm2.0.lean` by hand.
- Never cite the three unproved well-formedness theorems in the generated
  specification (`Step_is_wf`, `Step_read_is_wf`, `Step_pure_is_wf`).
- Review changes in `metrics/audit.txt` and `metrics/interface-manifest.json`. Explain any
  change to statement types, definition bodies, premises, specification patches
  or FunsExternal. Location changes and expanded audit coverage do not by
  themselves change a guarantee or the trust boundary.

## Changing Rust

1. Make the Rust change and run both Cargo test configurations.
2. `just extract`, then read the diffs of the generated `Funs*.lean` partitions
   to see which extracted functions changed.
3. For each changed function, repair its contract. If the effect statement is
   still true, callers need no change.
4. If the effect statement changed, repair the derived properties in the same
   module, then the callers that `just check` reports.
5. If a body-only change breaks proofs outside the function's own module, that
   is a rule 1 violation in existing code. Fix it by routing those proofs
   through the contract, not by patching each one.
6. Run the checks below.

## Before you finish

```sh
just check <modules you touched>   # confirm what the language server showed
just prove                         # once, at a completed migration checkpoint
just lint                          # layering, forbidden constructs, metric ratchet, links
just audit --no-build              # reuse that successful current build
```

When artifacts intentionally change, use `just audit --no-build --update` in
place of the last command and review both outputs. The audit checks public
result registration, semantic ownership, generated artifact freshness and axioms.
Repeated `#print axioms` sweeps during local iteration do not replace those checks.

Report in the change description: which contracts changed statement, any diff
in `metrics/audit.txt`, and any metric that moved.

For a multi-unit refactor, these are completed integration checkpoints. Use LSP,
targeted module checks and source architecture checks between edits; do not
repeat integrated builds or audits inside the same unfinished unit. Rebuild after
source changes before auditing an environment. Keep current guarantees and
reading paths within Results. Completed migration plans, rename
maps and source-digest review ledgers belong in Git history; the live audit
manifest, origin labels and metric ratchets remain maintained.

## Metrics

`python3 scripts/metrics.py` prints them; `metrics/baseline.json` records the
accepted values. The ratcheted ones may only improve.

The raw short-module count remains visible beside its exact structural
exemptions. Public-definition lines are reported separately by original module and area;
`lean_lines_by_area_with_interface_origin` retains relocated lines in their
original area. Reviewed merges with multiple origins use a joint origin bucket
and count its area once. Moving definitions is not proof deletion.

| Metric | Meaning | Direction |
| --- | --- | --- |
| `extra_unfold_files` | For each extracted function, the number of files that unfold it beyond the first, summed. Measures rule 1. | Ratchet down, goal 0 |
| `heartbeat_overrides`, `recdepth_overrides` | Raised elaboration limits. | Ratchet down |
| `theorems_with_15_or_more_binders` | Oversized statements. | Ratchet down |
| `bare_simp` | `simp` and `simp_all` without `only`. An upper bound on fragile uses. | Ratchet down |
| `modules_under_50_lines` | Modules that mostly pay import overhead. | Ratchet down |
| `layer_violations`, `sorry` | Must be 0. | Fixed at 0 |
| `lean_lines_per_rust_line` | Proof lines per Rust line, by area. About 10 to 20 is normal for this kind of project. | Watch |
| `max_import_depth`, `modules` | Shape of the build graph. Depth bounds parallel build time. | Watch |
| statement cone size (in `metrics/audit.txt`) | Lines a human must read to know what is claimed. | Watch, review every change |

## Existing proofs

Most of the tree predates this guide and breaks several rules; the metrics
record by how much. Apply the rules to everything you add or substantially
rewrite. Bring old proofs into line as part of a planned cleanup or when a
Rust change forces you to touch them. Do not mix a mass rewrite into an
unrelated change.
