# Proof health plan

Drafted 2026-11-12 against commit `81347267`. This plan gets the proof base into
shape for three upcoming Rust changes: a faster interpreter, a parallel
compilation interface, and a store abstraction for SpiderMonkey. It does not
implement those changes.

Supporting files:

- [../PROOF_ENGINEERING.md](../PROOF_ENGINEERING.md): the rules every step must follow.
- [research/store-api.md](research/store-api.md): field tree of `ExecutableInv`,
  reusable lemmas and draft theorem statements for Phase 3.
- [research/compiler-contracts.md](research/compiler-contracts.md): catalog of
  the compiler proofs and draft contracts for Phase 5.
- [research/wasm1-removal.md](research/wasm1-removal.md): inventory for Phase 1.
- [research/proof-idioms.md](research/proof-idioms.md): Aeneas tactic facts and
  examples from this codebase.
- `../scripts/`: `metrics.py`, `Audit.lean`, `merge_modules.py`,
  `strip_source_lines.py`, `check_links.py`. All five were run against the tree
  on 2026-11-12.

The research files were written by read-only agents. Statements marked [V] were
read in the code; statements marked [I] are inferences and were not compiled.
Line numbers will drift. Treat draft theorem statements as starting points: the
first thing to do with one is to make it typecheck.

## Decisions already made (2026-11-12)

- Wasm 1.0 is dropped from Rust and proofs (Phase 1). Only Wasm 2.0 is
  supported, with 3.0 to follow later as a replacement, not a second profile.
- Stripping line ranges from comments in the generated Lean is accepted (step
  0.4), and so is splitting the generated functions into several files (step
  2.2).
- Compiler completeness (`compile_with.profile_complete`) stays.
- `define_host` must leave the store unchanged when it fails; fix the Rust
  (step 3.0).
- Phase 5 has a checkpoint after its pilot (step 5.4). Work continues past it
  unless one of its stop conditions holds.
- CI runs on GitHub Actions (step 0.6).
- `lean/scripts/`, `lean/metrics/`, `lean/PROOF_ENGINEERING.md` and
  `lean/plan/` are committed. The plan directory was first meant to stay out of
  the repository; the user committed it on 2026-11-12 to move the work between
  machines. Guides other than the plan itself should still not link into
  `lean/plan/`, so it can be removed when the plan is done.
- Lemma names: old runtime `@[step]` lemmas (`within_spec`, `get_effect`) are
  renamed to `<rust path>.spec` only when their function gets a contract under
  this plan. No standalone rename sweep.
- Agents use the Lean language server (`lean-lsp-mcp`). The user registered it
  on 2026-11-12 as `lean-lsp` in their local Claude Code configuration. The
  guide's section "Use the language server" says how to work with it.
- Tactics: `omega` on goals purely about `Nat` and `Int`, and named
  `cases ... with | Ctor =>` arms, stay allowed, as the guide says. The tree has
  about 4,000 uses of each kind, and the upstream reasons for banning them
  (no knowledge of Rust integer types; slower re-checking in an editor) do not
  make proofs harder to maintain here.

## Additional decision (2026-11-13)

- Step 1.0 may raise `modules_under_50_lines` from 663 to 665: the new
  foundational `StoreParts.lean` and removal of the Wasm 1.0 wrapper from
  `EntryOfEnv.lean` are approved exceptions. Record 665 as the new ceiling;
  retain every other metric ratchet unchanged.
- Step 1.2 may raise `modules_under_50_lines` from 665 to 669: removing
  obsolete Wasm 1.0 proofs shortened five existing modules below 50 lines,
  offset by deleting one short module. This increase is approved; retain
  every other metric ratchet unchanged.
- Step 1.3 may raise `modules_under_50_lines` from 669 to 670: removing
  the redundant body certificate shortened `Profile/Body.lean` from 51 to
  42 lines. This increase is approved; retain every other metric ratchet
  unchanged.
- For the remaining step 2.1 merges, use targeted checks for each directory
  and defer full integration, lint and audit to the final clean build. The
  user approved this after the SpecExt and Runtime/Spec areas passed full
  integration: changes to foundational imports were repeatedly rebuilding
  most runtime proofs. This supersedes the per-area integration schedule
  below.
- More generally, avoid large rebuilds until needed: iterate with the language
  server and targeted builds, and batch broad validation at meaningful
  checkpoints rather than repeating it automatically after each small step.
  Retain Phase 2's clean-build benchmarks and final integration, lint and
  audit checks. Use local results for iteration without also polling PR CI.

- Step 2.2 may reorganize handwritten proofs to remove the compiler-to-interpreter
  dependency identified in preflight. The user approved separating interpreter
  slot proofs from shared representation facts; preserve theorem statements and
  proof bodies while adjusting their module locations and imports. This supersedes
  the prohibition on restructuring proofs for that dependency.
- The required equation-module split adds two foundational modules under 50
  lines; relocating the shared width equation also shortens Initializer below
  50 lines. Record these structural effects of the approved reorganization
  in the short-module baseline (50 to 53), retaining the other ratchets.

## Rules for whoever executes this plan

1. Read `AGENTS.md`, `DEVELOPMENT.md`, `lean/README.md` and
   `lean/PROOF_ENGINEERING.md` first.
2. Do the phases in order. Inside a phase, do the steps in order. Each numbered
   step is one commit with a short message saying what it does. Never add a
   `Co-Authored-By` line.
3. A full build (`just prove`) takes about 20 minutes on 16 cores. Iterate
   with the Lean language server tools (see "Use the language server" in the
   guide); if they are not among your tools, tell the user before starting.
   Confirm with `just check Itasca.Some.Module` and run `just prove` once at
   the end of a step. Never delete `lean/.lake/` or `lean/.build/`.
4. Every step ends with `just prove`, `just lint` and `just audit` passing
   (after Phase 0 creates the last two). If `metrics/audit.txt` changes, read
   the diff and say in the commit message what changed in the statement cone.
5. Never weaken, delete or restate a theorem in `lean/Itasca/Results/` unless
   the step says so. Never add `sorry`, an axiom, or `native_decide`. Never
   raise a heartbeat limit.
6. Stop and report to the user, without working around it, when:
   - a step's "Stop if" condition holds;
   - a proof still fails after three different repair attempts;
   - a headline theorem statement would have to change in a way the step does
     not describe;
   - a specification patch, `FunsExternal.lean`, or a pinned tool would have to
     change.
7. Scratch files go in `$TMPDIR`. Remove them when done.
8. Decisions the user has made are listed above; follow them. If a step turns
   out to need a decision that is not listed, stop and ask.

## Where we are (measured 2026-11-12)

| Fact | Value |
| --- | --- |
| Handwritten Lean | 278,190 lines in 2,418 modules; median module 82 lines; 663 under 50 lines |
| Rust | 12,815 lines |
| Clean build | 1,169 s on 16 cores; import chain 79 modules deep |
| Fixed cost per module | about 2.5 s to start Lean and load imports; a typical module's total is about 6 s under load |
| Proof lines per Rust line | compiler 44.7, store 28.5, interpreter 18.4, validator 10.9 |
| `extra_unfold_files` | 1,793 (`lower.FunctionCompiler.op` alone is unfolded in 69 files, 508 sites) |
| Heartbeat overrides | 266, most at 10 to 40 times the default |
| Theorems with 15 or more binders | 1,036; largest 56 |
| Statement cone | 9,785 handwritten lines (of which `Itasca/Binary` is about 3,900) |
| Axioms | all 16 headline theorems use only `propext`, `Classical.choice`, `Quot.sound` |
| Layer violations | 2 (runtime files importing `Itasca.Results.Unique`) |

Findings that drive the plan:

1. **The runtime chain is not closed.** Every runtime theorem assumes the store
   invariant `ExecutableInv`. No theorem shows a fresh store has it, and the
   public store API (`define_host`, `set_global`, `memory_mut`, `grow_memory`,
   and so on) has no theorems. The platform contracts `MemoryLaws` and
   `FloatOpsCorrect` have no proven instance.
2. **Build time is mostly fixed overhead times file count**, plus a long import
   chain. A change of one source-line comment in `Funs.lean` rebuilds every
   downstream module (tested: Lake rebuilt both a direct and an indirect
   importer although the `.olean` hash was unchanged).
3. **Compiler proofs are organized by property, not by function.** Each
   property re-walks the same extracted function with its own copy of an
   inversion tactic (34 `*_step` macros). One Rust edit breaks dozens of files.
4. **No automated guard** on axioms, layering or the statement cone, and no CI.
5. **Wasm 1.0** is a handwritten restriction layered on the Wasm 2.0
   specification. A `profile` parameter threads through 339 files and about 390
   theorems, the runtime carries a second instantiation rule for it, and it
   adds a handwritten specification extension to the trusted base.

## Phase order and why

| Phase | What | Why here |
| --- | --- | --- |
| 0 | Guardrails and baseline | Everything later is measured and checked by these. No proof changes. |
| 1 | Drop Wasm 1.0 | Deletion. Every later phase then touches less code. |
| 2 | Build structure | Makes Phases 3 to 5 cheaper to iterate on. |
| 3 | Close the runtime chain | Fills the largest hole in the guarantees with new, small proofs. |
| 4 | Readable statements | Small, and uses the Phase 3 results. |
| 5 | Compiler contracts | Largest refactor. Needs the fast build and the guardrails. Has a checkpoint after a pilot. |
| 6 | Readiness spikes | Short experiments that de-risk the three Rust changes. |

---

## Phase 0: guardrails and baseline

No proof is changed in this phase except step 0.4.

### 0.1 Wire the tooling into `just`

Add to `justfile` (root):

```make
# Proof-health metrics. See lean/PROOF_ENGINEERING.md.
metrics:
    @cd lean && python3 scripts/metrics.py

# Static checks that need no build: layering, metric ratchet, links, forbidden constructs.
lint:
    @cd lean && python3 scripts/metrics.py --violations
    @cd lean && python3 scripts/metrics.py --check metrics/baseline.json
    @cd lean && python3 scripts/check_links.py
    @cd lean && ! rg -n --glob '*.lean' --glob '!**/Generated/**' '\bsorry\b|\bnative_decide\b|^\s*axiom\b|^\s*admit\b' Itasca SpecExt

# Axioms and statement cone of the headline theorems. Builds first.
audit:
    @cd lean && lake build Itasca && lake env lean scripts/Audit.lean > metrics/audit.txt
    @git --no-pager diff --stat -- lean/metrics/audit.txt
```

Commit `lean/scripts/` in this step. Then create the baselines (also
committed):

```sh
mkdir -p lean/metrics
cd lean && python3 scripts/metrics.py --write metrics/baseline.json
just audit
```

Verify: `just lint` prints the two known layer violations and exits non-zero
(step 0.3 fixes them). `lean/metrics/audit.txt` starts with 16 lines ending in
`standard axioms only` and reports about 9,785 handwritten cone lines.

Also add `just lint` and `just audit` to the "Required checks" list in
`AGENTS.md` and to the command lists in `DEVELOPMENT.md` and `lean/README.md`.
In `lean/README.md`, the section "Proof checking" says there is no
dependency-layer or axiom check, and the section "Proof architecture" says
`just prove` enforces the layering. Rewrite both to say: `just lint` checks
layering and forbidden constructs, `just audit` checks axioms.

### 0.2 Adopt the proof engineering guide

- Link `lean/PROOF_ENGINEERING.md` from `AGENTS.md` (under "Proof discipline",
  add the sentence "Follow the proof engineering guide." with the words "proof
  engineering guide" linking to that file), from `lean/README.md` (top
  paragraph) and from `lean/PROOF_GUIDE.md` ("Names and proof units").
- `AGENTS.md`, "Proof discipline": replace "Use `just check Itasca.ModuleName`
  for iteration and `just prove` for integration." with "Iterate with the Lean
  language server tools, confirm with `just check Itasca.ModuleName`, and use
  `just prove` for integration."
- `lean/README.md`, "Setup": add the language server setup (the two commands
  in the guide's section "Use the language server").
- `DEVELOPMENT.md` says "The four guides have separate responsibilities". Make
  it five and add: "`lean/PROOF_ENGINEERING.md` describes how to write
  maintainable proofs".
- Add this lemma to `lean/Itasca/Support/Result.lean`, inside
  `namespace Itasca.ResultFacts` (it was compiled on 2026-11-12):

  ```lean
  /-- A returned result satisfies the postcondition of any specification of the same computation. -/
  theorem post_of_ok {α : Type} {m : Result α} {P : α → Prop} {r : α}
      (spec : m ⦃ P ⦄) (called : m = .ok r) : P r := by
    obtain ⟨r', run, post⟩ := WP.spec_imp_exists spec
    rw [called, Result.ok.injEq] at run
    exact run ▸ post
  ```

  Use it as `have post := ResultFacts.post_of_ok (f.spec args) called`. Writing
  `exact ResultFacts.post_of_ok ...` directly can fail to infer `P`.
  This file is imported by almost everything, so this step costs one full
  rebuild. Combine it with step 0.4 in one build.

### 0.3 Fix the two layer violations

`Itasca/Runtime/Integration/Execution/Ownership/SegmentInitialization.lean` and
`Itasca/Runtime/Compiler/Local/Source/SourceSlice.lean` import
`Itasca.Results.Unique`. Five runtime proofs use `Profile.module_unique`
(`Integration/Compilation/Certificate.lean`,
`Integration/Instantiation/InstantiateExecutableEventfulOrigin.lean`,
`Integration/Instantiation/InstantiateSource.lean`,
`Compiler/Module/CompileExecutable.lean`,
`Compiler/Module/CompileExecutableCapacities.lean`).

- In those five proofs replace `Profile.module_unique a b` with
  `ModuleBinary.ModuleEncodingWith.unique (Profile.code_prefix_unique _) a b`
  (this is the body of `Profile.module_unique` in `Results/Unique.lean`).
- In the two importing files replace `import Itasca.Results.Unique` with
  `import Itasca.Profile.BinaryUnique`.

Verify: `python3 scripts/metrics.py --violations` prints nothing; `just prove`.
Then rewrite the baseline (`--write metrics/baseline.json`); `layer_violations`
is now 0 and the ratchet keeps it there.

### 0.4 Stop source line numbers from invalidating the build

`Funs.lean` and `Types.lean` carry `Source: 'src/x.rs', lines 119:4-137:5` in
1,840 comments. Any Rust edit that shifts lines changes them and rebuilds
everything.

- In `lean/Makefile`, target `extract`: after the `$(AENEAS)` line add
  `python3 scripts/strip_source_lines.py Itasca/Generated/Types.lean Itasca/Generated/Funs.lean`.
- In target `extract-check`: after its `$(AENEAS)` line add
  `python3 scripts/strip_source_lines.py .build/extract-check/Itasca/Generated/Types.lean .build/extract-check/Itasca/Generated/Funs.lean`
  (before the two `cmp` lines).
- Run the script once on the committed files:
  `cd lean && python3 scripts/strip_source_lines.py Itasca/Generated/Types.lean Itasca/Generated/Funs.lean`.

Verify:

```sh
git diff -U0 -- lean/Itasca/Generated | rg '^[+-]' | rg -v '^(\+\+\+|---)' | rg -v 'Source:'   # must print nothing
just extract-check     # the pipeline reproduces the committed files
just prove
```

Update the sentences in `AGENTS.md` ("Rust comment and line-number changes also
require regeneration") and `DEVELOPMENT.md` ("Generated source locations change
when Rust lines move"): generated files now record the Rust file but not the
line range, so moving lines no longer changes them. `lean/README.md` says Aeneas
runs unmodified; add that one script removes line ranges from comments
afterwards and changes no definition.

Stop if: the first verify command prints anything.

### 0.5 Record the trust boundary accurately

Documentation only.

- `README.md`, "Trust boundary": the list covers the validator. Add the runtime
  items that `lean/README.md` already describes: the native wrappers in
  `src/runtime/native.rs` (allocator, `libm` floats, store identity counter),
  the 12 specification patches under `patches/` (name the builtin patch as the
  largest: 64 handwritten numeric definitions), the host-step extension
  `lean/SpecExt/Host.lean`, and the fact that the Lean model is sequential, so
  parallel use relies on Rust ownership.
- `lean/README.md`, "Specification gaps": add that the generated specification
  contains three unproved well-formedness theorems (`Step_is_wf`,
  `Step_read_is_wf`, `Step_pure_is_wf`), that nothing uses them, and that
  `just audit` fails if anything does.
- `lean/README.md`: SpecTec's Lean output contains no binary grammar (checked:
  no grammar declarations in `SpecTec/wasm2.0.lean`), so the handwritten grammar
  in `Itasca/Binary/` cannot currently be cross-checked against it.

Done when: `just lint` passes (links).

### 0.6 Continuous integration on GitHub Actions

There is no CI today. Add `.github/workflows/ci.yml` with three jobs. The YAML
below is a draft that has never run: develop it on a branch, push, and watch
the runs with `gh run watch` until all three are green. Before using an action,
check its current major version.

```yaml
name: CI
on:
  push:
    branches: [main]
  pull_request:

jobs:
  rust:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: git submodule update --init tests/third_party/wasm-spec
      - run: cargo test
      - run: cargo test --no-default-features

  lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: sudo apt-get update && sudo apt-get install -y ripgrep
      - uses: extractions/setup-just@v2
      - run: just lint

  prove:
    runs-on: ubuntu-latest
    timeout-minutes: 300
    steps:
      - uses: actions/checkout@v4
      - run: git submodule update --init vendor/spectec
      - uses: actions/cache@v4
        with:
          path: lean/.lake/packages
          key: lake-packages-${{ hashFiles('lean/lake-manifest.json', 'lean/lean-toolchain') }}
      - uses: leanprover/lean-action@v1
        with:
          lake-package-directory: lean
          build-args: "Itasca SpecExt"
          use-github-cache: false
          use-mathlib-cache: true
      - name: Audit axioms and statement cone
        working-directory: lean
        run: |
          lake env lean scripts/Audit.lean > metrics/audit.txt
          git diff --exit-code -- metrics/audit.txt
```

Design points, so you can repair the draft without changing its intent:

- The `prove` job always builds this project's proofs from scratch. Only the
  dependencies (`lean/.lake/packages`: Mathlib, Aeneas) are cached. A cached
  project build can report a stale success (lean4 issue 13449), and a proof
  checker must not.
- `lakefile.lean` reads a helper from `vendor/spectec`, so that submodule must
  be present. The Lean build does not need OCaml or the SpecTec tool.
- The audit step fails when the committed `metrics/audit.txt` differs from what
  the build produces, when a headline theorem uses a non-standard axiom, or when
  anything uses `sorry`.
- Expected problems: (1) Disk. Hosted runners have about 14 GB free; the
  dependency directory is about 8 GB and the project build about 5 GB locally.
  If the job runs out of space, add a first step that removes preinstalled
  software the job does not need (for example `sudo rm -rf /usr/share/dotnet
  /opt/ghc /usr/local/lib/android`) and report the space before and after with
  `df -h`. (2) Time. A public repository gets 4 cores, so expect the build to
  take roughly four times the 16-core time: over an hour now, less after
  Phase 2. Private repositories get 2 cores and billed minutes; check with
  `gh repo view --json visibility` and tell the user if it is private.
  (3) `lean-action` input names: read its `action.yml` if an input is rejected.
- Do not add `extract-check` to CI in this step. It needs the Charon and Aeneas
  toolchains built from source. Add it later as a separate workflow that runs
  only when `src/**`, `lean/Makefile` or `lean/toolchain.mk` change, with
  `~/.cache/itasca` cached.

After Phase 1 removes the Wasm 1.0 corpus, drop the `wasm-spec` submodule line
if no remaining test needs it.

Done when: all three jobs pass on a pull request, and a pull request that adds
`sorry` to any proof fails the `lint` job (try it once, then discard).
Stop if: the `prove` job cannot finish within its timeout or its disk. Report
the timing and `df -h` output.

---

## Phase 1: drop Wasm 1.0

The user decided this on 2026-11-12. Full inventory:
[research/wasm1-removal.md](research/wasm1-removal.md). Section numbers below
refer to it.

What this removes: the `Wasm1` validation profile from Rust and Lean, the Wasm
1.0 instantiation rule (segment bounds are pre-checked and the store rolls
back), the handwritten specification extension `lean/SpecExt/Wasm1.lean`, and
finally the `profile` parameter that threads through 85 extracted functions and
about 340 proof files. Removing `SpecExt/Wasm1.lean` and the `wasm_*` theorems
changes the trust boundary and the public claims; say so in the commit messages
and update `README.md`.

What it does **not** remove: `lean/Itasca/Binary/Wasm1/` (except `Subset.lean`)
and `lean/Itasca/Wasm1/Complete/`. The Wasm 2.0 instruction grammar is defined
as an extension of the Wasm 1.0 one (`Wasm2.Immediate.plain` wraps
`Wasm1.Immediate`), and the Wasm 2.0 completeness proofs dispatch base
instructions to `Wasm1.Completeness.*`. Those directories are the shared scalar
base. Do not delete or rename them in this phase.

There are four steps and three extractions. Each extraction rebuilds
everything, so do not add extraction points.

### 1.0 Preparation (Lean, tests and documentation only; no extraction)

The build stays green throughout.

1. Delete the Wasm 1.0 specializations in `Results/`: the five
   `metadata.validate_module.wasm_*` theorems, the three
   `stream.validate_streaming.wasm_*` theorems, and
   `ModuleBinary.ModuleEncoding.unique`. Remove their lines from
   `Itasca/Main.lean`.
2. Delete `Examples/Wasm1/ProfileBoundary.lean`. Port `Examples/Module/*.lean`
   and `Examples/Stream.lean` from `.Wasm1` to `.Wasm2` (they are Wasm 1.0 runs
   today; `Sections.lean` uses the Wasm 1.0 element and data encodings and needs
   the Wasm 2.0 flag forms). Move `Examples/Wasm1/Support.lean` to
   `Examples/Module/BodySupport.lean`. In `Examples/Wasm2/Module.lean`, drop the
   comparison with the Wasm 1.0 profile.
3. Delete the Wasm 1.0 wrapper lemmas listed at the end of "Delete outright" in
   section 3 (`ModuleEnv.SemanticPost` wrappers, `metadata.decode_segment_index.wasm1`,
   and the others named there).
4. Make every default explicit: the 65 `(profile : ValidationProfile := .Wasm1)`
   binders and the 5 `optParam ValidationProfile .Wasm1` signatures listed in
   section 4 lose their default, and each use that relied on the default passes
   the profile explicitly. Find them with `rg -n ':= \.Wasm1|optParam ValidationProfile' lean/Itasca`.
5. Move `storeParts` out of `Runtime/Store/Initialization/PrecheckLoop.lean`
   (about 30 other store files use it) into
   `Runtime/Store/Initialization/StoreParts.lean`, and update the imports.
6. Rust tests, fuzz targets and examples that only exercise Wasm 1.0 (list in
   section 1d): delete `tests/spec_tests.rs`, `tests/wasm1_profile.rs`,
   `tests/spec/`, `examples/wast_extract.rs`, the `wasm1_*` fuzz targets, and
   the Wasm 1.0 halves of the mixed files. Run both Cargo test configurations.
   These are not extraction inputs.

Verify: `just prove`, `just lint`, `just audit`, `cargo test`,
`cargo test --no-default-features`. In `metrics/audit.txt` the `wasm_*`
theorems are gone (also remove any from `headline` in `scripts/Audit.lean`;
today it lists only `profile_*` names).

### 1.1 Remove the Wasm 1.0 instantiation rule (extraction 1)

The enum still has two variants. No validator file changes.

Rust: delete `fn wasm1` (`src/runtime/store.rs`), the `if wasm1(...) { ... }`
block in `prepare_instance` (`src/runtime/store/instantiate.rs`, about lines
183 to 197), and `check_element_bounds` and `check_data_bounds`. Update the doc
comment of `Store::instantiate` in `src/runtime/native.rs`. Run both Cargo test
configurations, then `just extract`.

Lean (section 6):

- `Runtime/Store/Instantiation/PrepareInstanceClassified.lean` and
  `ResourceDecomposition.lean` each contain a split
  `cases profile : dataInst.module.profile with | Wasm2 => ... | Wasm1 => ...`
  on the deleted block. Keep the `Wasm2` arm's proof, without the split.
- Delete `Runtime/Store/Initialization/Precheck{Loop,Errors,Witness,Resources,CertifiedWitness,CertifiedResourceCauses,Source}.lean`,
  `Runtime/Store/Instantiation/PrecommitSource.lean`, and `SpecExt/Wasm1.lean`.
  `ElementPrecheckReady` / `DataPrecheckReady` and their uses in
  `InitializerCertificates.lean` go with them.
- `PrecommitError` (`Runtime/Store/Invariant/PrecommitError.lean`): remove the
  trap alternative and the profile parameter. Update its 15 user files.
- `PrecommitOrigins`: drop the `bounds` and `staging` fields.
- `InstantiationSourceOutcome`
  (`Runtime/Integration/Instantiation/InstantiateSource.lean`): remove the
  clause `∀ trap, error = .Trap trap → module.profile = .Wasm1 ∧ ...`. This
  changes the statement of `instantiate_with.spec`: rejection before
  publication now never reports a trap.

Verify: `just extract-check`, `just prove`, `just lint`, `just audit`. The
audit diff shows `InstantiationSourceOutcome` and `PrecommitError` smaller and
nothing from `SpecExt.Wasm1`.
Stop if: loops other than `prepare_instance_loop10` and `loop11` were
renumbered in `Funs.lean` (check `git diff --stat` and the loop names). The
inventory expects only those two to disappear.

### 1.2 Single-variant enum (extraction 2)

This step cannot be split: once `Wasm1` leaves `Generated/Types.lean`, 82 proof
files that name it stop compiling, starting with the lowest layers.

Rust: change the enum to `pub enum ValidationProfile { Wasm2 }` (`src/lib.rs`).
At every site in section 1a, delete the `Wasm1` arm and keep a one-arm
`match profile { ValidationProfile::Wasm2 => ... }`. Keep the functions
`check_opcode`, `check_block_type`, `check_table_byte`, `check_table_target`
and `check_table_count` as trivial functions, so the generated bodies keep
their shape. Keep every `profile` parameter. Do not remove `Error` variants or
limits yet. Update public docs that show `ValidationProfile::Wasm1`. Run both
Cargo test configurations, then `just extract`.

Before repairing anything, look at how `code.check_opcode` and
`metadata.decode_value_type` now read in `Funs.lean` and write two lines in the
commit message about the shape of a `match` on a one-constructor type. The
inventory could not verify this in advance. If Aeneas rejects or warns on the
one-arm `match`, stop and report.

Lean, bottom-up in import order (each bullet builds before the next starts;
use `just check`):

1. `Binary/Module.lean`, `Binary/ModuleUnique*.lean`: delete the Wasm 1.0
   grammar alternatives (`ElementEncoding`, `DataEncoding`, `BodyEncoding`,
   `CodeEncoding`, `ModuleEncoding`, the `ValueTypeAllowed` family). Keep
   `ModuleEncodingWith` and its `codeRel` argument: `Binary/Module.lean` cannot
   import the Wasm 2.0 token grammar without an import cycle.
2. `Profile/Types.lean`; then `Module/Readers`, `Module/Const`,
   `Module/Sections`, `Module/Env`.
3. `Wasm2/BodySpec.lean`, `Wasm2/Invariant.lean`, then `Wasm2/Control`,
   `Wasm2/Complete`, `Wasm2/Trace`.
4. `Profile/*`, `Module/Elab`, `Module/Soundness.lean`.
5. `Contracts.lean`, `Stream/*`.
6. The runtime compiler files with a `Wasm1` arm, and
   `Runtime/Compiler/Body/Reader/Replay/OpcodeClassification.lean`.
   `ReaderOpcode .Wasm1` there means "the base opcode set handled by
   `code.step`": restate it as a profile-free predicate `BaseOpcode`; do not
   delete it.
7. `Results/*`.

How to repair each kind of site (sections 2 and 5):

- `cases profile with | Wasm1 => A | Wasm2 => B`: keep `B`.
- A hypothesis or field `profile = .Wasm1 → P`: delete it and every proof of
  it. This changes the number of fields of `Wasm2.State.running/closed`,
  `Pending`, `Wasm2.Validated`, `AcceptedBody`, `AcceptedTrace`,
  `ModuleEnv.Valid`, `ModuleConditions`, `EntryTyped`, `CodeEntry.Typed` and
  `HeaderEncoding`, so anonymous-constructor patterns elsewhere need one fewer
  component.
- A hypothesis `profile ≠ .Wasm1`: delete it and its arguments.
- Definitions listed under "Trivial at Wasm2": delete them and their uses.
- Definitions listed under "Real content at Wasm2": keep the `Wasm2` branch as
  the definition. Keep the name and the `profile` parameter in this step.

Then delete the files listed under "Delete outright" in section 3:
`Wasm2/ProfileAgreement.lean`, `Wasm2/ProfileFrames.lean`,
`Binary/Wasm1/Subset.lean`, `Binary/ProfileEncoding.lean` (replace
`ProfileConsumed` by `Wasm2.Consumed`), `Wasm1/ProfileSyntax.lean` (three files
import it without using it; they import `Itasca.Support.ControlTranslation`
instead), `Profile/Instructions.lean`. Trim `Wasm2/ProfileFilters.lean` to the
lemmas about the now-trivial `check_*` functions.

Verify: `just extract-check`, `just prove`, `just lint`, `just audit`,
both Cargo test configurations. `rg -n 'Wasm1' lean/Itasca --glob '!**/Generated/**'`
matches only namespace and file names of the shared base (`Wasm1.Immediate`,
`Wasm1.BytesAt`, `Wasm1.Completeness`, imports of `Binary.Wasm1.*` and
`Wasm1.Complete.*`), never the constructor `.Wasm1`.
Stop if: a completeness theorem in `Results/` can no longer be proved with its
current statement.

### 1.3 Remove the `profile` parameter (extraction 3)

Rust: remove `ValidationProfile`, every `profile` parameter (section 1b), the
fields `CodeBatch.profile` and `ExecutableModule.profile` with their accessors,
the five trivial `check_*` functions, `limits::MAX_TABLES`,
`limits::MAX_RESULTS`, `Error::MultipleTables` and `Error::TooManyResults`.
Do not rename `step_profile`. Update `README.md`, crate docs and tests. Run
both Cargo test configurations, then `just extract`.

Lean: 85 extracted functions lose an argument; about 2,650 references in 340
files change (200 of them under `Runtime/Compiler`). The repair is mechanical:
delete the `profile` binder and the argument. Go bottom-up in the same import
order as 1.2. Also:

- Rename the headline theorems `profile_spec`, `profile_total`,
  `profile_sound`, `profile_complete`, `profile_complete_with_metadata`,
  `profile_complete_spec` to the same names without `profile_`, in `Results/`,
  `Main.lean` and `scripts/Audit.lean`.
- Merge `Profile.Body` into `Wasm2.Validated` (they are equivalent at Wasm 2.0
  by `Body.iff_validated`), and drop `executable.profile = profile` from
  `Integration.CompilationCertificate`.
- `ModuleElaboration.Profile raw profile` keeps its content (export-name
  uniqueness, at most one memory, declared `ref.func` targets). Rename it
  `ModuleElaboration.Restrictions raw`.
- Delete what is left of `Wasm2/ProfileFilters.lean`.
- Update every guide: `README.md`, `DEVELOPMENT.md`, `AGENTS.md`,
  `lean/README.md`, `lean/PROOF_GUIDE.md`, `lean/Itasca/Runtime/README.md`.

Verify: as in 1.2, plus
`rg -n 'ValidationProfile|\bprofile\b' lean/Itasca --glob '!**/Generated/**'`
prints nothing outside prose. Rewrite `metrics/baseline.json`.

This step is the largest of the four and purely mechanical: after 1.2 the
parameter is inert. Do it here, so later phases do not carry the parameter.


---

## Phase 2: build structure

Goal: cut clean-build CPU by about 40% and stop unrelated Rust edits from
rebuilding everything. Record `time just prove` from a clean state
(`just clean && time just prove`) once before step 2.1 and once after each
step, and write the numbers into the commit messages.

### 2.1 Consolidate small modules

Completed 2026-11-13: [results and clean-build comparison](notes/step21-results.md).

Background, from simulation on the current tree: merging files freely within
directories (2,422 to about 570 modules) halves CPU but triples the estimated
critical path, so the build gets slower. `scripts/merge_modules.py` only merges
when the estimated critical path does not grow. Its plan for today's tree is
2,423 to 778 modules in 496 groups, estimated CPU down 43%, critical path
unchanged. Regenerate the plan now, because Phase 1 changed the tree:

```sh
cd lean
python3 scripts/merge_modules.py plan --cap 1000 > plan/merge-plan.json   # takes a few minutes
```

Apply it one directory at a time. For each directory that contains a group
target (list them with
`python3 -c "import json,os;print('\n'.join(sorted({os.path.dirname(g['target'].replace('.','/')) for g in json.load(open('plan/merge-plan.json'))['groups']})))"`):

1. `python3 scripts/merge_modules.py apply plan/merge-plan.json --dir <directory>`.
   It prints `merged N modules into <Target>` for each group.
2. `lake build <every Target printed>`.
3. Fix what fails. Expected causes, in order of likelihood:
   - A duplicate declaration name, because two former files defined the same
     `private` name inside a namespace the planner did not see. Rename the later
     one after its section and update its uses in that section.
   - A `simp` that behaves differently because a lemma tagged `@[simp]` or an
     instance from an earlier section is now in scope. Make that call
     `simp only [...]` with the lemmas it needs.
   - An ambiguous name, because an earlier section declared a name that the
     later section used to resolve elsewhere. Qualify the name.
   Do not move or rewrite proofs beyond these fixes.
4. If a group cannot be fixed with three attempts: `git checkout -- Itasca SpecExt`,
   delete that group's object from `plan/merge-plan.json`, and repeat from 1.
5. Commit the directory.

Work through the areas in this order, running `just prove` and `just lint` at
the end of each area: `SpecExt`, `Itasca/Runtime/Spec`,
`Itasca/Runtime/SourceMachine`, `Itasca/Runtime/Representation` and `Platform`,
`Itasca/Runtime/Interp`, `Itasca/Runtime/Store`, `Itasca/Runtime/Compiler`,
`Itasca/Runtime/Integration`, then the validator directories.

The tool writes each former module as a `/-! ## Name -/` heading and an
anonymous `section`, which is the convention already used in files such as
`Runtime/Integration/Invocation/Behaves.lean`. It writes a one-line file
docstring listing the sections. Leave that docstring as is; do not invent
descriptions.

After the last area:

- `just lint` reports broken documentation links to deleted files. Point each
  at the merged file.
- Prose in `lean/README.md`, `lean/PROOF_GUIDE.md` and
  `lean/Itasca/Runtime/README.md` that names a deleted module: update the name.
  Find candidates with `rg -o 'Itasca/[A-Za-z0-9/]+\.lean' lean/*.md lean/Itasca/Runtime/README.md | sort -u`
  and check each path exists.
- `python3 scripts/metrics.py --write metrics/baseline.json`.

Done when: `modules` in the metrics is under 900, `max_import_depth` is at
most 79, `just prove` passes, and the clean build time is recorded.
Stop if: the clean build is slower than before. Report the two times.

### 2.2 Split the generated functions by Rust area

Completed 2026-11-13: [results and timing](notes/step22-results.md). The user
authorized the proof reorganization resolving the [preflight blocker](notes/step22-blocker.md).

The user approved this on 2026-11-12. Unlike step 0.4, it does more than touch
comments: a script moves each generated declaration, unchanged, into one of six
files and adds imports between them. It cannot change what a declaration means
(same text, same namespace, same `open`s, and a missing or misplaced
declaration fails the build). Say in `lean/README.md` that this is a second
transformation between Aeneas and the proofs. What it buys: an edit to the interpreter or the
store no longer rebuilds the validator and compiler proofs, which are more than
half of the tree, and the first 108 seconds of every build shrink to about 30
for the validator chain.

Today one `Funs.lean` (63,708 lines, 108 s to build) sits under 2,235 modules,
so an interpreter edit rebuilds the validator and compiler proofs. The
declarations partition cleanly (checked with a script on 2026-11-12: 1,724
declarations, no `mutual` blocks, and dependencies only run forward in this
order):

| File | Rust paths | Declarations | Lines |
| --- | --- | --- | --- |
| `FunsValidator.lean` | everything not under `itasca::runtime` | 746 | 15,950 |
| `FunsRuntimeCommon.lean` | `runtime::{bytecode, operators, value, platform}` and items directly in `runtime` | 66 | 5,643 |
| `FunsCompiler.lean` | `runtime::compiler` | 315 | 16,929 |
| `FunsStore.lean` | `runtime::store` except `store::instantiate` | 50 | 1,518 |
| `FunsInterp.lean` | `runtime::interp` | 491 | 21,101 |
| `FunsInstantiate.lean` | `runtime::store::instantiate` | 56 | 2,541 |

Each file may use declarations from the files above it in the table.

1. Write `lean/scripts/split_funs.py`. Input: `Itasca/Generated/Funs.lean`.
   - The file is a 26-line header (through `namespace Itasca`), then
     declarations, then `end Itasca`.
   - Split the declarations with the regular expression `(?m)^(?=/-- \[)`: every
     declaration starts with a doc comment `/-- [itasca::path::name]`. Classify
     each chunk by that path using the table above.
   - Write the six files, each with the original header, the chunks of its
     class in original order, and `end Itasca`. In each header, after the
     existing imports, add `public import Itasca.Generated.<Earlier>` for every
     file above it in the table.
   - Rewrite `Funs.lean` as an umbrella: the original first comment lines,
     `module`, then `public import` of the six files. Nothing else.
   - The script must fail if a chunk has no `/-- [` path, or if the number of
     chunks written differs from the number read.
2. Call it from `lean/Makefile` in `extract` and `extract-check`, after
   `strip_source_lines.py`. `extract-check` must compare all seven files.
3. `lake build Itasca.Generated.Funs`, then `just prove`. Nothing else should
   need to change, because `Funs` still exports everything.
4. Narrow the imports so proofs depend only on what they use:
   - The seven handwritten files that `import Itasca.Generated.Funs` directly:
     the validator ones import `Itasca.Generated.FunsValidator` instead.
   - Split `Itasca/Runtime/Equations.lean` (it forces equation lemmas for 13
     functions) into `Equations/Bytecode.lean` (the seven `runtime.bytecode.*`
     functions; imports `FunsRuntimeCommon`) and `Equations/Interp.lean` (the six
     `runtime.interp.*` functions; imports `FunsInterp`). Keep `Equations.lean`
     as an umbrella importing both.
   - Of the 21 files that import `Itasca.Runtime.Equations` directly, change
     those under `Runtime/Compiler`, `Runtime/Representation` and
     `Runtime/Platform` to import `Itasca.Runtime.Equations.Bytecode` plus the
     generated file they need (`FunsCompiler`, `FunsStore`). Let build errors
     tell you which.
5. Check the result with the import graph: no module under `Itasca/Binary`,
   `Handler`, `Visitor`, `Wasm2`, `Profile`, `Module`, `Stream` or
   `Runtime/Compiler` may transitively import `Itasca.Generated.FunsInterp`.
   Add this as a rule in `layer_violations` in `scripts/metrics.py`.
6. Update `lean/README.md` ("Generated sources") and `AGENTS.md` ("Coupled
   sources") to name the seven files and the splitter.

Done when: step 5's check passes and `just prove` passes.
Stop if: after step 4 a compiler proof still needs `FunsInterp`. Report the
import chain (`lake exe graph` is not needed; walk imports with the functions in
`scripts/metrics.py`). Do not restructure proofs to break the chain.

---

## Phase 3: close the runtime chain

Goal: a caller can go from nothing to a store with host functions and
instantiated modules using only proved steps, and the platform contracts are
shown satisfiable. All details, including the field tree of `ExecutableInv`,
existing lemmas with locations, extracted signatures and draft statements, are
in [research/store-api.md](research/store-api.md). Section numbers below refer
to it.

Put the new proofs in `lean/Itasca/Runtime/Integration/Api/`, one module per
group of operations: `StoreCreate.lean`, `StoreDefine.lean`, `StoreWrite.lean`,
`StoreGrow.lean`, `StoreRead.lean`. Name each theorem after the extracted
function with `.spec`, tag it `@[step]`, and follow rules 1 and 2 of the guide:
destructure the result in the binder and use an exhaustive `match` on the Rust
result instead of the `out.1 = ... →` implications in the drafts.

Facts every step needs (all verified in the code):

- `CumulativeStoreMutation` plus `ExecutableInv.update` covers operations that
  leave `id`, `funcs`, `types`, `instances`, `externs` and `limits` equal. It
  does not cover `define_host_with` or `define_extern_with`.
- Every handle argument needs an "issued" premise (`Store.ExternalIssued`),
  because the Rust indexes without a bounds check and the model then fails.
  Every value argument needs `Store.IssuedValue`.
- Allocating operations need `Platform.AllocCorrect`; memory operations need
  `Platform.MemoryLaws`.

### 3.0 Make `define_host` atomic (Rust, one extraction)

Completed 2026-11-13: [implementation and validation](notes/step30-results.md).

Today `define_host_with` (`src/runtime/store.rs`) interns the type first and
checks the object limit and reserves afterwards. If one of those later checks
fails, the store keeps a newly interned type. The user decided to fix this.

Change the Rust so every check that can fail happens before the store changes:

```rust
/// Index of the interned type equal to `ty`, or `self.types.len()` if there is none.
fn find_type(&self, ty: &FuncType) -> usize {
    let mut i = 0;
    while i < self.types.len() && !same_func_type(&self.types[i], ty) {
        i += 1;
    }
    i
}

/// Fails unless `count` more objects fit under the object limit.
fn room_for(&self, count: usize) -> Result<(), ExecError> {
    let n = /* the same sum as today's `room` */;
    if n >= self.limits.max_objects || count > self.limits.max_objects - n {
        Err(ExecError::Exhausted(ResourceLimit::Objects))
    } else {
        Ok(())
    }
}
```

- `room` becomes `self.room_for(1)`.
- `intern_type` starts with `let i = self.find_type(ty);` in place of its own
  loop. Nothing else in it changes.
- `define_host_with` becomes: compute
  `let fresh = self.find_type(&ty) == self.types.len();`, then
  `self.room_for(if fresh { 2 } else { 1 })?`, then
  `reserve::<A, _>(&mut self.funcs, 1)?`, then
  `let signature = self.intern_type::<A>(&ty)?;`, then push the function. The
  second `room` call goes away: a fresh type takes one of the two slots that
  were checked. `intern_type` already leaves the store unchanged when it fails.
- Add a regression test to `tests/runtime_api.rs`: a store whose
  `max_objects` is 1; `define_host` with a new type returns
  `Exhausted(Objects)`; a following `define_extern` succeeds (before the fix it
  fails, because the leaked type used the slot).

Then both Cargo test configurations and `just extract`.

Lean repairs, all small. `room` and `intern_type` changed body, so the proofs
that look inside them break:

- `room_spec` (`Runtime/Store/Api/Define.lean`): add
  `runtime.store.Store.room_for.spec` (returns `.Ok ()` exactly when
  `objectCount s < s.limits.max_objects.val` and
  `objectCount s + count.val ≤ s.limits.max_objects.val`) and derive `room_spec`
  from it with `count = 1`.
- `Runtime/Store/Invariant/InternTypes.lean`: the loop lemma about
  `intern_type_loop` becomes `runtime.store.Store.find_type.spec` (the result
  is the first index whose type equals `ty`, or the length); `intern_type_effect`
  steps through it. Its statement (`InternEffect`) does not change.
- `Runtime/Store/Invariant/InternTypeCauses.lean` and
  `Runtime/Store/Preparation/AllocationErrors.lean` unfold `intern_type`; repair
  them by stepping through `find_type.spec`. `AllocationErrors.lean` has a
  tactic table keyed on function names; add `find_type` to it if a case is
  missing.

Verify: `just extract-check`, `just prove`, `just lint`, `just audit`. No
headline statement changes.
Stop if: any theorem statement outside the four files above has to change.

### 3.1 Shared helpers

Completed 2026-11-13: [helpers and validation](notes/step31-results.md).

1. Make the vector index lemmas public once. `global_index_given` /
   `global_index_mut_given` (`Runtime/Interp/State/Globals.lean`) and
   `table_access_index_given` / `table_access_index_mut_given`
   (`Runtime/Interp/State/TableAccess.lean`) are private copies of the same two
   facts. Add one public pair next to `vec_index_given` in
   `Runtime/Interp/Relations/Fetch.lean`, use it in both files, delete the
   private copies.
2. Add `MemoryGrowth.extends` and `TableGrowth.extends` (each concludes
   `Extend_store (decodeStore view code before) (decodeStore view code after)`)
   next to `MemoryGrowth.shape` in `Runtime/Store/Api/GrowthEffects.lean`.
   Proof outline in section 5.10 and 5.11.
3. Add `ExecutableInv.append_hosts` and `Shape.of_allocated` (section 5.0) in
   `Integration/Api/StoreCreate.lean`.

### 3.2 Fresh store

Completed 2026-11-13: [contract and validation](notes/step32-results.md).

`runtime.store.Store.with_identity.spec` (section 5.1). Needs the premise
`0 < id.val`. The native wrapper guarantees it by starting its counter at 1;
say so in the docstring.

### 3.3 Definitions

In this order: `define_extern_with` (5.3), `define_host_with` (5.2),
`define_memory_with` (5.4), `define_table_with` (5.5), `define_global_with`
(5.6).

After step 3.0, `define_host_with` leaves the store unchanged when it fails,
so its error case says `after = store`, like the other definitions. The draft
in section 5.2 and obstacle 2 of the research file describe the Rust before
that fix; ignore the "error path changes the store" caveat there. The
transport lemma `ExecutableInv.append_hosts` is still what proves the success
case.

### 3.4 Writes and growth

`set_global` (5.7), `set_table` (5.8), `memory_mut` (5.9), `grow_memory_with`
(5.10), `grow_table_with` (5.11). For `memory_mut` the postcondition quantifies
over the bytes written back and requires the same length.

### 3.5 Reads

`global`, `memory`, `table_size`, `table_get`, `func_type`, `extern_identity`,
`export`. Each theorem: under the issued-handle premise the function returns
normally, and a successful result equals the corresponding component of
`decodeStore view code store` (for example the value returned by `global` is
`sourceValue`-equal to `(decodeStore view code store).GLOBALS[i].VALUE`).
`decode_global_owned` (`Runtime/Store/Invariant/ValueRead.lean`) is the
existing read-side lemma. `export` needs
`a.store = store.id → a.index.val < store.instances.length` as its premise.

### 3.6 Handle persistence

One lemma per handle kind: `ExternalIssued`, `IssuedValue` and `ValueInStore`
survive every operation above. State them over the relations the operations
return (`StagedPrefix`, `CumulativeStoreMutation`, and length monotonicity of
`externs`), so they need no knowledge of the operations.

### 3.7 Publish the results

- New `lean/Itasca/Results/Store.lean` restating the theorems of 3.2 to 3.5 as
  one-line projections, in the style of the other `Results/` files.
- Import it in `Itasca/Main.lean` and list the theorems in its docstring.
- Add them to `headline` in `scripts/Audit.lean`.
- `Itasca/Runtime/Contracts.lean`, section "Store state": say that the
  invariant is established by `with_identity` and preserved by every store
  operation and by `instantiate_with` and `invoke_with`, and that a host
  callback discharges `HostWorldSound` by composing these theorems.
- Update `README.md` and `lean/README.md` ("Execution boundary").

### 3.8 The in-repo memory satisfies the memory laws

In `lean/Itasca/Runtime/Platform/VecMemory.lean` define the dictionary that
`src/runtime/native.rs` builds (`impl MemoryBuffer for VecMemory`):

```lean
def vecMemory {A : Type} (allocator : runtime.platform.Alloc A) :
    runtime.platform.MemoryBuffer runtime.platform.VecMemory where
  new_zeroed n := runtime.platform.VecMemory.new_zeroed_with allocator n
  bytes m := runtime.platform.VecMemory.as_bytes m
  bytes_mut m := runtime.platform.VecMemory.as_bytes_mut m
  grow m n := runtime.platform.VecMemory.grow_with allocator m n
```

and prove `Platform.MemoryLaws (vecMemory allocator) view` from
`Platform.AllocCorrect allocator`, with `view m` the slice of `m.data`. The
extracted functions are near line 59,730 of `Funs.lean`; `grow_with` contains
one loop, proved with `loop.spec_decr_nat` (see
[research/proof-idioms.md](research/proof-idioms.md), A5). The match between
this definition and the Rust `impl` is by inspection; say so in the docstring.

### 3.9 The float contract is satisfiable

In `lean/Itasca/Runtime/Platform/FloatWitness.lean` construct one
`runtime.platform.FloatOps Unit` whose every operation returns the bits of the
first element of the specification's result list, and prove
`Platform.FloatOpsCorrect` for it. Ingredients that exist:

- `SpecExt/Builtins/Float/FirstChoice.lean`: `ReplyFamily` and one
  `*_reply_family` lemma for each of `fadd_`, `fsub_`, `fmul_`, `fdiv_`,
  `fsqrt_`, `fceil_`, `ffloor_`, `ftrunc_`, `fnearest_`, `demote__`. Each result
  list is a singleton or a NaN set, hence non-empty.
- `SpecExt/Builtins/Float/Encoding.lean` and `Decoding.lean`: round trips
  between `fN` and bits (`float_roundtrip_32`, `float_roundtrip_64`,
  `float_bits_roundtrip_32`, `float_bits_roundtrip_64`).
- `SpecExt/Builtins/Float/Wf.lean`: well-formedness of results, which the round
  trips require.

The eight `convert` fields have singleton lists. The definition may be
`noncomputable`. This proves the contract is not vacuous; it says nothing about
`libm`.

Stop if: a result list can be empty for some input, or a result is not
well-formed. That would be a defect in the trusted float definitions. Report
the operation and input.

### 3.10 Closed examples

In `lean/Itasca/Examples/Runtime.lean`, importing only `Itasca.Main`:

1. `fresh_store_valid`: for `vecMemory grantAll`, the store from `with_identity`
   with `id = 1` satisfies `ExecutableInv`.
2. `host_only_invoke`: create that store, `define_host_with` one function of
   type `[] → []`, and apply `runtime.interp.invoke_with.behaves` with
   `Examples.trapHost`, `grantAll`, the float witness of 3.9 and `vecMemory`.
   Every hypothesis of `behaves` must be discharged inside the example; none may
   be a parameter. The `fun_invoke` premise needs the source-level invocation of
   a host function: `decode_host_function`
   (`Runtime/Store/Invariant/HostSignature.lean`) gives the `HostFunction` fact.
3. Compile and instantiate the empty module
   `0x00 0x61 0x73 0x6d 0x01 0x00 0x00 0x00` using the compiler completeness
   theorem. This needs `Compiler.CompileEligible` for a concrete module, which
   nothing in the tree discharges today. Compiler completeness is being kept,
   so this example matters: it is the first evidence that the theorem's
   premises can be met. If it takes more than three attempts, stop and report
   exactly which premise blocks it.

Done when (phase): `just prove`, `just lint`, `just audit` pass;
`metrics/audit.txt` lists the new headline theorems with standard axioms only.

---

## Phase 4: readable statements

### 4.1 Name the parts of results

The headline runtime statements address results as `out.2.2.1`. Projections of
this kind occur 1,361 times in 268 files; this step changes only the statement
layer:

- `Results/Invoke.lean`, `Results/Instantiate.lean`, `Runtime/Contracts.lean`.
- The definitions they mention: `InvocationBehaves`
  (`Integration/Invocation/Behaves.lean`), `ExecutableWorldRecordedOutcome` and
  `InvocationRejected` (`Integration/Invocation/Outcomes.lean`),
  `ExecutableWorldInvocationSourceCause` (`Integration/Invocation/Resources.lean`),
  `InstantiationSourceOutcome` and `InstantiationResourceCause`
  (`Integration/Instantiation/InstantiateSource.lean`), `HostWorldSound`,
  `HostRetention`, `NoHostStackOverflow`.

In each, bind the tuple in the postcondition
(`⦃ (result, execution, store', platform', values) => ... ⦄`) and give
definitions separate named parameters instead of one tuple parameter. Proofs
that use these definitions will need `obtain ⟨...⟩` or `rcases` where they used
projections; change only what stops compiling.

Verify: `rg -n '\.2\.2|\.2\.1' lean/Itasca/Results lean/Itasca/Runtime/Contracts.lean`
prints nothing. `metrics/audit.txt` changes only in line counts of the
definitions named above.

### 4.2 A map of the runtime argument

Add a section "The argument in ten definitions" to
`lean/Itasca/Runtime/README.md`. For each of these, give its file, a two
sentence description taken from its docstring, and what uses it:
`SpecExt.StepH` and `StepsH`, `Store.decodeStore`, `Store.CodeInterpretation`,
`SourceMachine.AState` with its step relation and `SourceMachine.decode`,
`Interp.Machine.Execution`, `Compiler.ExecutableModuleFunctions`,
`Integration.ModuleCodeRel`, `Integration.CompilationCertificate`,
`Integration.ExecutableInv`, `Integration.CumulativeStoreMutation`. Then one
paragraph stating the chain: extracted interpreter, related by
`Machine.Execution` to the flat source machine, which `SourceMachine.decode`
maps to SpecTec configurations stepped by `StepsH`.

Do not describe anything you have not read. Mark the section "needs human
review" in the commit message; the user will check it.

---

## Phase 5: compiler contracts

Goal: each extracted compiler function is unfolded in one module, and every
property is derived from that module's contract. Read
[research/compiler-contracts.md](research/compiler-contracts.md) fully before
starting; it catalogs every theorem that unfolds `emit`, `enter` and `op`, the
34 per-property step tactics, and draft contracts. The Rust is in
`src/runtime/compiler/`; the proofs are in `lean/Itasca/Runtime/Compiler/`
(`Local/` is the layer that changes).

The findings that shape the work:

- Properties are proved in inversion style from
  `called : f ... = .ok (status, after)`. Keep that: the contract for a function
  is an effect relation plus one inversion theorem, one totality theorem and,
  where completeness needs it, one availability theorem. An equation
  `f ... = .ok (g ...)` is impossible for functions that call the allocator,
  because `AllocCorrect` leaves the allocator's answer free.
- Helpers are not re-unfolded by callers today; each property has its own lemma
  about each helper. So contracts must be introduced bottom-up, helpers first.
- `op` has 508 unfold sites; 204 of them only take the dead-code branch.

### 5.1 Quick win: the dead branch of `op`

Add (in the module that will own `op`, start with
`Compiler/Local/Lowering/Emission/Lowering.lean`):

```lean
theorem runtime.compiler.lower.FunctionCompiler.op.dead {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a b : U32) (bits : U128) (dead : before.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits =
      runtime.compiler.FunctionCompiler.observe ops before state
```

Prove it once by `unfold`, then rewriting the `if` with `dead`. Keep the proof
term small: see obstacle 1 in section 6 of the research file and the technique
in `Compiler/Local/Lowering/Simd/SimdDispatch.lean`. Then replace every
`unfold runtime.compiler.lower.FunctionCompiler.op at h` that is followed by
`rw [if_neg ...] at h` with `rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ dead] at h`.
Find the sites with
`rg -n -A2 'unfold runtime.compiler.lower.FunctionCompiler.op' lean/Itasca | rg 'if_neg'`.

Done when: `python3 scripts/metrics.py --top` shows `op` in at most about 45
files (from 69) and the build passes. Update the baseline.

### 5.2 Pilot A: `emit`

`runtime.compiler.FunctionCompiler.emit` (Rust `src/runtime/compiler/mod.rs`,
`fn emit`) is unfolded by 14 theorems in 13 files, listed in section 1.1 of the
research file. Three near-contracts already exist: `Emitted` with
`compiler_emit`, `compiler_emit_success`, and `compiler_emit_available_frame`.

1. Prerequisite (obstacle 11): move `budget_push_success` and
   `control_add_success` down next to `budget_push` in
   `Compiler/Local/Relations/Layout/LayoutProofs.lean`, so the contract module
   can sit as low as `Compiler/Local/Lowering/Emission/Emit.lean`.
2. In `Emit.lean`, define the effect relations from the draft in section 5 of
   the research file (`EmitFrame` for any status, `EmittedExact` for success)
   and prove exactly three theorems that unfold `emit`:
   - `emit.inv`: from `called : emit ops before instruction = .ok (status, after)`
     and `AllocCorrect`, conclude `EmitFrame before after` and, when
     `status = .Ok ()`, `EmittedExact before after instruction`.
   - `emit.total`: `emit ... ⦃ _ => True ⦄` under `AllocCorrect` and the three
     fit premises of today's `compiler_emit`.
   - `emit.available`: today's `compiler_emit_available_frame`, restated with
     `EmittedExact`.
3. Reprove each of the other 11 theorems from `emit.inv` without unfolding
   `emit`. Keep their names and statements, so their callers do not change.
   Frame facts (cursor, reachable, height, tables, capacity metadata) follow
   from `EmitFrame` by `rw`; arithmetic facts from `EmittedExact`.
4. `compiler_emit` and `compiler_emit_success` become corollaries of the three.

Done when: `emit` is unfolded only in `Emit.lean` (check with
`python3 scripts/metrics.py --top`), no statement outside `Emit.lean` changed,
and no heartbeat limit was raised. Record for the checkpoint: number of files
touched, lines added and removed, and the build time of `Emit.lean` before and
after (`just profile Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit`).

### 5.3 Pilot B: `enter`

`runtime.compiler.control.FunctionCompiler.enter` (Rust
`src/runtime/compiler/control.rs`) is unfolded by 20 theorems in 18 files
(section 1.2). It calls `emit`, `pc`, `observe` and pushes a control frame; it
has 9 leaf paths.

1. First give `pc` and `observe` contracts the same way as `emit` (they are
   unfolded in 13 and 25 files; lists are in the research file, section 3).
2. Define the effect of `enter` as in the draft (`enterPrefix`, `enterIfPc`,
   `Entered`). Prove the publication suffix shared by all paths once as its own
   lemma, then the three prefixes (obstacle 9).
3. Three theorems unfold `enter`: `enter.inv`, `enter.total`,
   `enter.available`. All other 17 are reproved from them. The hand-copied body
   `scopePublication` in `Compiler/Local/Capacity/EnterAvailability.lean` is
   deleted in favor of the effect relation.
4. Properties that are invariants (`SourceCoordinates`, `FixupBudget`,
   `ControlMapPublication`) are derived with the transport lemmas that already
   exist (`SourceCoordinates.advance`, `Emitted.source_coordinates`,
   `FixupBudget.ordinary`, `ControlMapPublication.enter_effect`).
5. Two properties depend on states inside the body (`compiler_enter_observation`,
   `control_entry_coordinates`; obstacle 4). If the effect relation cannot
   express them, add the intermediate state as an existential field of
   `Entered`. Do not leave them unfolding `enter`.

Done when: `enter`, `pc` and `observe` are each unfolded in one module.

### 5.4 Checkpoint

Test the claim the refactor exists for: on a scratch branch make a small
body-only Rust change to `emit` (for example add a redundant check that cannot
fail), re-extract, and count the Lean files that fail. Discard the scratch
branch.

Then report to the user, for `emit` and `enter`: files touched, net line
change, heartbeat overrides removed, per-module build time before and after,
how many per-property step macros (`*_step`, `*_effect`, `*_close`) became
unused, and the count from the experiment above.

Continue with 5.5 without waiting, unless one of these holds. If one does,
stop and wait for the user:

- the body-only Rust change broke more than three Lean files;
- the pilot increased the total lines under `Runtime/Compiler`;
- a heartbeat limit had to be raised, or a contract proof takes more than 120
  seconds to build;
- a statement outside the contract modules had to change.

### 5.5 Rollout

Same method, bottom-up, in this order (unfold counts are today's):

1. Remaining helpers: `copy` (14 files), `patch` (13), `pair` (11),
   `finish_op` (14).
2. Control: `control.FunctionCompiler.branch` (29), then the visitor callbacks
   `on_else` (16), `on_end` (17), `on_br_if` (17), `on_br` (16),
   `on_unreachable` (15), `on_return` (13), `on_br_table` (11).
3. `op`: one arm equation per opcode class, all in the one module that unfolds
   `op`; then one effect per tail (`finish_op`, `observe`, `copy; observe`,
   `pair; finish_op`, `simd_op`); then derive every property per class by
   rewriting with the arm equation. Never case on `runtime.bytecode.Instr`. The
   56 hand-restated `run` equations in the `Literal*` files are replaced by the
   arm equations.
4. `simd.FunctionCompiler.simd_op` (11), `initialize.constant` (4).

After each function: delete step macros and helper lemmas that nothing uses any
more (the tables run under `try` and name lemmas that do not exist, so check
uses with `rg`, not by whether the build passes). Remove file-scoped heartbeat
options from every module you rewrite; if a theorem still needs one, scope it
with `in` and decompose it if it needs more than 1,000,000.

Compiler completeness stays, so every function keeps its `.available` theorem
and the completeness proofs (about 29,000 lines that only
`compile_with.profile_complete` needs) are migrated like the rest.

Done when (phase): `extra_unfold_files` for `runtime.compiler.*` functions is
0, `heartbeat_overrides` under `Runtime/Compiler` is below 40 (from 191), and
the ratio `lean_lines_per_rust_line.compiler` has gone down.

The same method applies to `Runtime/Interp` (`interp.dispatch` is unfolded in
31 files, `simd.simd` in 29) and `Runtime/Store`. Do those after the compiler
only if the user asks; the interpreter proofs will be reworked by the
performance changes anyway.

---

## Phase 6: readiness spikes

Short experiments, each ending in a written note for the user under
`lean/plan/notes/`. No production code.

1. **Extraction limits for the interpreter design.** Aeneas at this pin does
   not support unsafe code, concurrency, `return` inside nested loops, or
   instantiating a generic with a mutable reference (its `README.md`,
   "Targeted Subset And Current Limitations"). On a scratch crate, try to
   extract: (a) an inner loop that holds `&[Instr]`, `&mut [u64]` and a memory
   slice across iterations; (b) dispatch through a table of function pointers;
   (c) a handler-per-instruction design using an enum match. Report what
   extracts and what the Lean looks like.
2. **Store abstraction.** `runtime.store.Store M` appears in 532 Lean files and
   its fields are read directly in 325. Write a one-page design for a Rust
   trait that the interpreter uses instead of the concrete struct, with a Lean
   ghost function `view : S → runtime.store.Store M` and laws, following the
   existing `MemoryBuffer` / `view` / `MemoryLaws` pattern. List which Phase 3
   theorems become the trait's laws.
3. **Parallel compilation.** The compiler already drives the streaming
   validator with a private scheduler (`Compiler/Module/CompileSchedulerAssembly.lean`
   and neighbors). Write down what the public contract would be, modeled on
   `Itasca/Contracts.lean` (`StreamSource.Coherent`, `StreamScheduler.Provenance`,
   the `CallbacksTotal` and `Accepts` contracts), with
   `Integration.CompilationCertificate` as the unchanged conclusion.

---

## Open questions for the user

1. **Ask Aeneas upstream for an option to omit line ranges** from source
   comments? The pinned revision has none. With it, `strip_source_lines.py`
   could be deleted. The user will consider this later; it blocks nothing.
