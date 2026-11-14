# Step 5.4 compiler pilot checkpoint

Completed 2026-11-13. Production integration, lint, and audit pass. The body-only
Rust mutation requires repairs in exactly one Lean file; full downstream
integration then passes. The pilot triggers the line-growth stop condition.
Step 5.5 has not begun and awaits the user's decision.

## Pilot measurements

| Measurement | Emit (5.2) | Enter, PC, observe (5.3) |
| --- | --- | --- |
| Lean files touched | 16 | 24 |
| Net compiler lines | -292 | +948 |
| Compiler heartbeat overrides removed | 0 | 6 |
| Cached module profile before | 7.54 s | EnterIf: 15.30 s |
| Cached module profile after | 7.10 s | EnterIf: 9.25 s; EnterContracts: 15.27 s |
| Newly unused per-property macros | 0 | 0 |

The final Emit profile supersedes the intermediate step 5.2 measurement of
7.03 seconds. EnterContracts is new: comparing EnterIf alone would omit its
cost. These separate cached module profiles do not establish an integrated
build speedup. Two pre-existing orphan step macros and their three exclusive
helper tactics were removed; they did not become unused because of this pilot.

Compiler source grows from 96,845 to 97,501 lines: +656 (0.7%). Compiler
heartbeat overrides fall from 191 to 185, with none raised. Every contract
owner builds below the 120-second gate. Module count rises from 788 to 789;
maximum import depth stays 64. Consumer theorem headers are preserved. The
copied scopePublication executable and its obsolete availability helper are
removed. No trust boundary changes.

Step 5.1 separately removed 194 compiler lines by replacing 204 repeated
op.dead proofs in 41 consumers with one equation. That reduction precedes the
pilot baseline and does not offset its line-growth gate.

## Body-only Rust mutation experiment

A scratch branch from d96e607e repeated the existing self.pc()? in Rust emit.
Failure of the first check still exits immediately. Its success leaves state
unchanged, so the second check succeeds with the same result. Extraction took
200 seconds and changed only the generated emit body in FunsCompiler.lean.
Before mutation, the unchanged owner passed with Lake rebuilding disabled,
confirming the copied cache was usable.

The initial target check reported errors in exactly one handwritten Lean file,
Emit.lean. Repair changed only the inv, total, and available proof bodies
(+13 net lines), preserving all theorem headers, imports, and budgets.
The repaired owner passed on its first check in 7.26 seconds. Full cached
just prove then passed all 4,069 jobs in 834 seconds with no further changes.
Thus the measured repair count is one file, including downstream consumers.
This is evidence for this mutation, not a claim about every possible Rust edit.

The scratch Rust/generated/Lean changes and branch were discarded. The build,
dependency, extraction, and copied specification caches were retained in a
TMPDIR archive; logs, source diffs, and timing records were also retained.
No experimental source changes entered the production branch.

## Production validation and decision

Cached just prove passes all 4,069 jobs, with the final successful run taking
583 seconds. An earlier integration attempt found a helper-name collision with
an existing reader EntryPrefix; renaming the new helper EnterEmissionPrefix
resolved it. Just lint and just audit pass, and the headline audit is unchanged.

The only triggered step 5.4 stop condition is: "the pilot increased the total
lines under Runtime/Compiler". The +656-line result meets that condition.
Wait for the user's decision before step 5.5; the relaxed general repair-count
rule does not waive this specific pilot gate.
