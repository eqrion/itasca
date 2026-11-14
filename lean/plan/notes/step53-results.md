# Step 5.3 results

Implemented 2026-11-13. EnterContracts owns the three entry body traversals:
enter.inv, enter.total, and enter.available. EnterIf retains the existing
adapters. The split keeps the contract owner below 1,500 lines.

The inversion contract retains allocator-independent frame, prologue arithmetic,
and final observation evidence. Exact publication and slot monotonicity carry
AllocCorrect. Totality also covers the existing law-free empty-condition
rejection, with its source-coordinate bound. Availability retains conditional
instruction storage requirements: dead entry and ordinary blocks do not require
emission capacity. The successful budget effect records exactly one control and
the selected prefix's zero or one instruction.

Seventeen existing entry proofs derive from the contracts. The copied
scopePublication executable definition and its availability helper are removed.
PC and observation unfolds now each have one owner. Shared operand, loop, and
height helpers moved down without changing their statements. A source comparison
finds 373 preserved existing theorem headers across the changed files; the only
removed theorem is the obsolete scope_publication_available helper.

All focused derivations pass Lean checks. The integrated owner check passes
3,294 jobs, including the new module and both lower helper moves. Direct checks
of all six canonical emit/enter contracts and both new observation facts report
only propext, Classical.choice, and Quot.sound. Cached full integration passes all 4,069 jobs after renaming a new internal
helper to avoid a collision with the existing reader EntryPrefix. The final
successful run takes 583 seconds; the headline audit is being completed at
step 5.4.

This step touches 24 Lean files and adds a net 948 compiler lines. Together with
step 5.2's 292-line reduction, the pilot grows compiler source from 96,845 to
97,501 lines (+656, about 0.7%). This triggers the checkpoint's line-count stop
condition; rollout requires a decision after the remaining checkpoint evidence
is collected. No unrelated source was removed to offset the increase.

Compiler heartbeat overrides fall from 191 to 185; none was raised. No
per-property macro becomes unused as a result of the pilot. Two pre-existing
unused step macros and their three exclusive helpers were removed.

Cached profiles: Emit 7.54 seconds before and 7.10 after; EnterIf 15.30 before
and 9.25 after; the new EnterContracts module takes 15.27 seconds. These are
separate module profiles, not an integrated-build speedup measurement. Module
count is 789 and maximum import depth remains 64. No Rust, generated source,
consumer theorem statement, or trust boundary changed.

Checkpoint validation: cached `just prove` passes all 4,069 jobs; `just lint`
and `just audit` pass. The headline audit is unchanged.
