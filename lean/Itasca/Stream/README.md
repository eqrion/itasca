# Streaming orchestration

This layer proves the generic driver and its contiguous-source/synchronous-worker
adapter. The driver orders environment parsing, code dispatch, worker retirement
and tail validation. Issued batches fix their environment, byte region and identity;
only actual successful worker operations advance validation evidence.

[Soundness](SubmissionSound.lean) proves acceptance invariants;
[Totality](RetirementAndFraming.lean) proves normal return under returning callbacks;
[DriverRegions](Completeness.lean), [SplitComplete](SubmissionSound.lean) and
[Completeness](Completeness.lean) construct acceptance from independent premises.
[SliceComplete](Completeness.lean) supplies the contiguous adapter used by
whole-module validation.

Read [Interface/Streaming](../Results/Definitions/Streaming.lean#L479) for the distinct source,
scheduler and worker-provenance premises and [Results/Stream](../Results/Stream.lean)
for the public statements. Entry offsets refer to the code region, function
starts to batch code, and operator positions to instruction bodies. Lean models
sequential computations; native lifetimes and concurrent provenance remain
embedding obligations.
