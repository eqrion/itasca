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

## Ongoing control, opcode, and driver consolidation

The working batch now covers branch and table-branch effects, control callbacks,
opcode-class equations, SIMD, function entry and finish, signature and environment
capture, collection and code-region scanning, compile entry, submission, and the
public compiler driver. Existing consumer theorem headers are preserved; newly
introduced contracts carry the operational premises that their consumers prove.
Initializer leaf and loop contracts are still being checked. This is a progress
record, not a completed integration checkpoint.

Focused checks have reduced compiler heartbeat overrides to nine. The remaining
three outside InitializerTotal are in two unchanged modules whose default-budget
checks timed out. The six InitializerTotal overrides will be revisited after its
loop migration. No proof budget has been raised.

The generated-unfold metrics scanner now recognizes actual tactic-list heads,
including multiline generated declarations, and excludes negative simp entries
and names used only as arguments to other lemmas. Thirteen Python regression
tests pass. Re-parsing the previous committed checkpoint with the corrected
scanner raises its global extra_unfold_files from 1,221 to 1,259; this measurement
correction is separate from proof improvements.

A current source snapshot has 25 extra compiler unfold files, all in initializer
functions, and zero layering violations. Compiler source totals 102,071 lines
versus 97,670 at the preceding checkpoint: the phase-wide line-ratio goal remains
unmet. Consolidating 99 private scalar-property wrappers into shared opcode groups
already saved 1,048 lines, with all three affected full-source checks passing.
Further shared-loop and unused-helper consolidation is ongoing.

Full integration and the headline axiom/statement audit remain pending. The
current source has been checked with targeted direct Lean invocations using
cached imports; these do not substitute for the final integrated build.

The control readiness bundles and all seven consumers pass full-source checks.
Fifteen initializer-helper and driver modules also pass after coordinated artifact
refresh, followed by all eleven modules affected by the 511-line obsolete-tactic
cleanup. The bundled global/data loop engine and six exact-header adapters pass
their combined checks. Lint now passes, including the original high-arity and
short-module ratchets. Documentation links and whitespace checks pass.

The element leaf owner, its three consumers, and the global/data/element loop
adapters pass targeted checks. The compact segment-emission owner now passes at
default budgets after fixing tactic focus around continuation subgoals. Its six
consumers and segment-loop instantiations are the next targeted batch.

All twelve modules in the combined initializer owner/donor batch pass direct
checks. InitializerTotal takes 7.4 seconds in this check, compared with 45.3 seconds
in an earlier targeted run before its loop consolidation; this is a module-level
observation, not an integrated build benchmark. Its full source also passes with
all five remaining heartbeat overrides removed. Compiler overrides are now three,
all in the two unchanged modules noted above. The only remaining duplicate compiler
unfold owner is initialize.lower (four files, three extra).

The full top-level initializer owner and all four exact-header consumer adapters
pass staged checks. End/Else property traversals have been consolidated, removing
196 lines; both complete owners pass at default budgets. A whole-tree suffix
audit found no missed compiler-generated unfold owners among unqualified tactic
heads: the remaining suffix matches refer to local terms and handwritten helpers.

After top-level initializer integration, the compiler duplicate-unfold metric is
zero and three heartbeat overrides remain. Lint passes. Both compacted control
owners and all seven direct consumers pass actual-source checks. A pre-integration
snapshot has 101,813 compiler lines (49.2 Lean lines per Rust line), so the
phase-wide line-ratio acceptance criterion remains unmet. Full build/audit are
still pending; phase 5 is not marked complete.

The frozen rollout snapshot contains 101,427 compiler lines and a ratio of 49.0.
For the phase-wide comparison, the actual pre-phase-5 baseline is commit
0b6edf2e: 97,039 lines and a ratio of 46.9 (the 96,845-line pilot baseline follows
step 5.1). The remaining increase is 4,388 lines, about 4.5%. Compiler ownership
and heartbeat targets are met; the line-ratio target is not.

## Validated rollout checkpoint

Full `just prove` passes all 4,097 jobs; `just lint` and `just audit` pass.
The final integration repairs restore an accidentally removed theorem opening
line and normalize a vector length before an arithmetic proof. Existing consumer
statements remain unchanged. Thirteen metrics-scanner regression tests pass.

All 34 headline theorems retain standard axioms only. The audit diff records
17 declarations moving to lower modules; declaration identities, statement-cone
line counts/totals, and the axiom report are otherwise identical. There is no
trust-boundary change and no Rust/generated/specification change in this rollout.

Final compiler measurements: zero duplicate unfold owners, three heartbeat
overrides (from 191), and 101,428 lines. The pre-phase baseline is 97,039 lines:
+4,389 (+4.5%), with the Lean/Rust ratio rising from 46.9 to 49.0. This last
phase-wide acceptance gate remains unmet, so phase 5 is not marked complete.
The proof-health ratchet baseline records the validated improvements; it does
not waive the separate phase-wide line-ratio requirement.

Cleanup removes unused tactic support and migration-orphan helper adapters after
whole-repository reference checks. This includes the old PC/local availability
adapters as well as the separately inventoried branch, source, environment,
collection, submission, and initializer wrappers. Canonical contracts and the
headline results remain available; the checked consumer theorem headers are
preserved. End/Else shared property traversals save 196 lines, and one shared
mapping proof replaces duplicated semantic initialization arguments.
