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

## Unreachable and accessor checkpoint

The next batch gives on_unreachable a single unfold owner and canonical
inversion, totality, and exact-budget availability contracts. Fifteen consumer
proofs now use those contracts; their focused combined check passes. The
operational effect retains failed emission state and final observation calls,
so allocator-independent frame claims and partial-error behavior are preserved.

ExecutableModule.env and tail now have owner equations in Initializer. Existing
consumers use those equations, and env.spec moves there with its header unchanged.
Budget.reject has one reflexive equation in LayoutProofs. Copy availability is
strengthened to distinguish an elided unchanged state from an exact emission;
its existing consumer statement is unchanged. Four entry normalization lemmas
move unchanged from EnterContracts into LayoutProofs for lower-level reuse.

Twenty-six additional compiler heartbeat overrides are removed after full-module
checks at default limits. Two attempted removals still time out and are retained.
Compiler heartbeat overrides are now 150. Compared with the preceding helper
checkpoint, global extra_unfold_files falls from 1,280 to 1,221; compiler duplicate
unfold-owner files fall from 341 to 282. Compiler lines rise from 97,463 to 97,670
(+207); the phase-wide line-ratio goal remains outstanding. There are 791
handwritten modules and no new layering violations. The targeted consumer batch passes all 3,947 jobs. The exact checkpoint source
snapshot passes lint. Existing consumer headers remain unchanged; the intentional
Copy.available strengthening is the only changed shared theorem header.

Full integration and headline audit remain deferred. Branch, else, end and return
contracts are ongoing work, excluded from this checkpoint's metrics and claims.
