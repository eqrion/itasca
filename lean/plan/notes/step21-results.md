# Step 2.1 results

Completed 2026-11-13. All 493 planned groups across 165 directories were
merged, removing 1,627 source modules. No groups were dropped. Each directory
passed targeted checks before its commit. Final Lean sources are at `7d1c58ce`;
guide and metric updates are at `64a77b61`.

## Clean-build comparison

Both runs used `/usr/bin/time -p just prove`, with the project build cache
moved aside before `just clean`. Dependency caches and the previous project
caches were preserved. No other CLI builds competed with either benchmark.

| Measurement | Before (`b5eb7283`) | After (`7d1c58ce`) |
| --- | ---: | ---: |
| Wall seconds | 1998.60 | 1057.94 |
| User seconds | 8531.34 | 5644.86 |
| System seconds | 7985.91 | 2505.30 |
| Build jobs | 5676 | 4049 |
| Handwritten modules | 2402 | 775 |
| Maximum import depth | 79 | 64 |
| Modules under 50 lines | 670 | 50 |
| Extra unfold files | 1743 | 1380 |

Wall time fell 47.1%; total CPU time fell 50.7%. Both plan thresholds pass:
fewer than 900 handwritten modules and import depth at most 79.

## Validation and proof repairs

The final clean build, lint, audit, documentation-link check, and diff whitespace
check passed. Rust, generated definitions, specification files, and pins were
unchanged.

Three merge-related repairs passed on their first attempt: explicit simp lemmas
in Spec.Simd.IntegerMinMax; explicit selection of the original scalar-cast rule
in Interp.Memory.MemoryCoreStep; and disambiguation of the duplicate
slots_fit_accepts helper in Compiler.Local.Capacity.GlobalCapacity. No proof
statements or headline theorem premises changed.

All 16 headline theorems use only standard logical axioms. The audit retains
1,682 handwritten declarations / 9,486 lines, 2,616 specification declarations /
25,640 lines, and 2,720 extracted declarations / 62,484 lines. Every changed audit
row matches the module mapping in merge-plan.json; declaration names and line
counts are identical. There is no trust-boundary change.
