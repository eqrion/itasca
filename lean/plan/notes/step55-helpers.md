# Step 5.5: remaining compiler helpers

The user approved continuing past the pilot's +656-line gate. The first rollout
batch consolidates copy, pair, patch, and finish_op. Each now has exactly one
unfold owner and canonical inversion, totality, and availability contracts.
Existing consumer signatures are preserved, including allocator-independent
frames, elided-copy availability, and exact instruction/pair budget effects.
Patch totality retains the existing known-branch-at-index premise; it does not
claim arbitrary out-of-range indexing returns normally.

FinishEffect records emission rejection or successful emission followed by
observation, retaining the intermediate state for coordinate consumers.
Whole-tail equality adapters use owner equations; property consumers use
contracts. Pair owns its low index helpers, moved unchanged to LayoutProofs.
CallbackDemand moved unchanged to the finish_op owner to avoid an import cycle.

All 358 existing theorem headers across the changed files compare unchanged.
The batch changes 27 Lean files, including the new Pair owner. Compiler lines
fall from 97,501 to 97,463 (-38). Global extra_unfold_files falls from 1,317 to
1,280. Compiler heartbeat overrides fall from 185 to 176: patch's old override
and eight broad source/capacity overrides are removed. Matching recursion
overrides are removed too. No budget is raised; no trust-boundary change.

Targeted integration passes all 3,486 jobs. Focused language-server checks and
subsequent just check validate the three source/capacity modules at default
budgets (3,324 jobs including cached dependencies). Existing per-property
macros remain referenced; none became newly unused. Two tactic blocks
accidentally removed during mechanical migration were restored unchanged before
the successful consumer check.

The helper checkpoint passes just lint in an exact staged source snapshot,
separate from the ongoing branch migration. Direct checks of all twelve new
contracts report only propext, Classical.choice, and Quot.sound.
Full integration and the headline audit remain deferred to the next broad
rollout checkpoint, under the user's approved validation schedule. Phase 5.5
continues with branch and control callbacks; this note does not mark it complete.
