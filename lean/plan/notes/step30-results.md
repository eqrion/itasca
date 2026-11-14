# Step 3.0 results

Completed 2026-11-13. define_host_with checks whether one or two object slots
are needed, checks that capacity, and reserves function storage before interning
the signature. room delegates to room_for(1); intern_type reuses the read-only
find_type search. The rest of interning is unchanged.

The max_objects=1 regression passes: a fresh host signature is rejected with
Exhausted(Objects), and a following define_extern succeeds. Both full Cargo test
configurations pass. The new test required an explicit default Store type.

Regeneration changes only FunsStore.lean: room/room_for, find_type and its loop,
intern_type, and define_host_with. All other generated partitions and Types are
unchanged. Both extraction and the separate reproducibility comparison pass.

Lean repairs are confined to the four planned files at their consolidated
locations: Api/DefineTable, Invariant/Rollback, Invariant/FunctionStagingCauses,
and Preparation/AllocationStorage. Existing room_spec, InternEffect, and caller
statements are unchanged. New normal-result classification lemmas keep error
callers from unfolding room. LSP and targeted checks pass; one constructor
injectivity spelling correction was needed, with no substantive proof retries.

Also narrowed the unused FunsStore import in Representation.StoreCapacity to
FunsRuntimeCommon and imported FunsStore explicitly in DefineTable. LSP and a
targeted check validate this import-only change. Compiler imports now reach
neither generated interpreter functions nor generated store functions.

The cached integration build passes all 4,058 jobs in 203.04 seconds (640.36
user, 597.11 system). No clean rebuild was performed for this step. Lint and
documentation/whitespace checks pass. Extra unfolding files fall from 1,380 to
1,379 and bare simp calls from 8,826 to 8,822; other ratchets do not worsen.

The audit passes with all 16 headline theorems using standard axioms only.
Handwritten and specification statement-cone totals are unchanged. Extracted
sources change from 2,720 declarations / 62,484 lines to 2,722 / 62,349:
the new room_for and find_type helpers replace the larger mutable-store search
flow. No headline statement or external/specification trust boundary changes.
The public store API preservation theorems follow in the later Phase 3 steps.
