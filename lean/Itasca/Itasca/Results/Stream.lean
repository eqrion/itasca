import Itasca.Stream.RetirementAndFraming
import Itasca.Results.Definitions.Streaming
import Itasca.Stream.SubmissionSound
import Itasca.Stream.Completeness

open WebAssembly

/-!
# Streaming validation

Soundness, termination and completeness of `stream.validate_streaming` for Wasm 2.0. Each claim rests on its own embedding premises from
`Itasca/Results/Definitions/Streaming`: soundness on `Stream.Source.Describes` and `Stream.Scheduler.Provenance`,
termination on `Stream.Source.CallbacksTotal` and `Stream.Scheduler.CallbacksTotal`, completeness on
`Stream.Source.CanonicalAvailable` and `Stream.Scheduler.Accepts`.

Soundness and completeness identify the data segments and shared code descriptors in the returned module.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Binary Module.Elaboration

/-- Acceptance of the streaming driver certifies the concatenated bytes, its returned
environment, and the tail it actually received, and bounds their size by the module cap.
Soundness requires coherent source views and worker provenance. Read errors and callback failures
are allowed, and neither callback termination, a canonical region split nor prevalidated bodies
are needed. -/
theorem stream.validate_streaming.sound {S V : Type}
    (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop)
    (provenance : Stream.Scheduler.Provenance visitor Tracks)
    (id : U64) (state : S) (v v' : V) (env : metadata.ModuleMetadata (alloc.sync.Arc metadata.CodeMetadata))
    (data : Slice U8)
    (coherent : Stream.Source.Describes source state data)
    (tracked : Tracks id [] v)
    (accepted : stream.validate_streaming source visitor id state v = .ok (.Ok env, v')) :
    Module.Sound.Validated data env ∧
      data.length ≤ limits.MAX_MODULE_BYTES.val := by
  obtain ⟨regions, concatenated, coherent⟩ := coherent
  obtain ⟨run, valid, bounded⟩ := stream.validate_streaming.sound_core source visitor Tracks
    provenance id state v v' env data regions.env regions.code regions.tail coherent concatenated tracked accepted
  exact ⟨valid, bounded⟩

/-- `stream.validate_streaming` returns success or an error on arbitrary bytes when the source and
scheduler callbacks return. Neither successful batches, source coherence nor scheduler provenance
is a termination premise. -/
theorem stream.validate_streaming.total {S V : Type}
    (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (v : V)
    (source_returns : Stream.Source.CallbacksTotal source state) (scheduler_returns : Stream.Scheduler.CallbacksTotal visitor) :
    ∃ r, stream.validate_streaming source visitor moduleId state v = .ok r :=
  stream.validate_streaming.total_core source visitor moduleId state v source_returns scheduler_returns

/-- Independently encoded, elaborated, typed modules within the limits are
accepted by `stream.validate_streaming` under canonical available reads and an accepting
scheduler that returns actual worker results, without assuming worker success.
The shared descriptors and data segments in the returned module match the raw module. Completeness fails if reads are unavailable or workers do not accept. -/
theorem stream.validate_streaming.complete {S V : Type}
    (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (config : stream.StreamingConfig) (Queued : U64 → List Stream.Batch.Issued → V → Prop)
    (scheduler_accepts : Stream.Scheduler.Accepts visitor config Queued)
    (id : U64) (state : S) (before : V)
    (data : Slice U8) (raw : Binary.Module)
    (encoded : ModuleEncodingWithinLimits raw data.val)
    (signatures : ModuleSignaturesWithinLimits raw)
    (elaborated : Elaborates raw (moduleOf raw))
    (typed : Module_ok (moduleOf raw)) (restricted : Restrictions raw)
    (available : Stream.Source.CanonicalAvailable source state data) (queued : Queued id [] before) :
    ∃ env after,
      stream.validate_streaming source visitor id state before = .ok (.Ok env, after) ∧
      Matches env raw ∧ AccessorTypes env raw ∧ Queued id [] after := by
  obtain ⟨env, after, run, called, matched, accessors, retained⟩ :=
    stream.validate_streaming.complete_core source visitor config Queued scheduler_accepts id state before
      data raw encoded signatures elaborated typed restricted available queued
  exact ⟨env, after, called, matched, accessors, retained⟩

end Itasca
