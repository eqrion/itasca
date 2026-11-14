# Step 5.2 results

Completed 2026-11-13. Emit now has exactly three body traversals, all in
Lowering/Emission/Emit: inv, total, and available. EmitFrame holds without
allocator laws; code growth and exact successful effects are conditional on
AllocCorrect. Availability retains its original AllocationAvailable premises.
This preserves both law-free and allocator-dependent caller statements.

Eleven facet proofs and the two compatibility wrappers derive their facts from
these contracts. Four shared vector/arithmetic helpers moved to LayoutProofs;
the PC availability lemma moved to Emit. All 261 existing theorem headers in
the changed files are preserved, including relocated helpers. The change touches
16 Lean files, adds 336 lines and removes 628, reducing compiler source from
96,845 to 96,553 lines. No heartbeat override or trust boundary changed.

The Emit target and its dependencies compile. A direct Lean scratch check
imports the compiled Emit and checks all eleven new facet bodies plus both
compatibility wrappers with their exact statements and needed stable definitions.
All thirteen pass. The three contracts use only standard axioms. Lint, links,
and whitespace checks pass. Full consumer integration and the headline audit
remain batched at step 5.4, under the approved validation schedule.

Cached per-module profiling took 7.54 seconds before and 7.03 seconds after step 5.2. The final pilot profile is 7.10 seconds.
The metrics scanner now reports emit unfolding in only its owner module;
extra_unfold_files falls from 1357 to 1339 and bare_simp from 8815 to 8798.

Checkpoint validation: cached `just prove` passes all 4,069 jobs; `just lint`
and `just audit` pass. The headline audit is unchanged.
