import Itasca.Stream.Definitions
import Itasca.Results.Definitions.Streaming
import Itasca.Stream.WorkersAndSource

/-!
# Worker batches

Results for workers issued by `stream.validate_streaming`: normal return preserves
operation provenance, independently valid issued contents are accepted, and
successful finishing certifies every entry and consumption of the issued bytes.

`Stream.Batch.Reachable` requires actual worker operations, never assigned cursor
values or assumed worker success. Contracts for arbitrary intermediate cursors
remain in `Stream/WorkersAndSource`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Binary

/-- Running `stream.CodeBatch.validate_all` terminates in a reachable state, including on invalid
bytes and stored errors. -/
theorem stream.CodeBatch.validate_all.spec
    (issued : Stream.Batch.Issued)
    (batch : stream.CodeBatch) (issued_bounds : issued.Bounded)
    (entry_bounds : CodeEntry.Bounds issued.env) (reachable : Stream.Batch.Reachable issued batch) :
    stream.CodeBatch.validate_all batch ⦃ after => Stream.Batch.Reachable issued after ⦄ :=
  stream.CodeBatch.validate_all.reachable issued batch issued_bounds entry_bounds reachable

/-- `stream.CodeBatch.validate_all` returns a reachable batch. -/
theorem stream.CodeBatch.validate_all.total
    (issued : Stream.Batch.Issued)
    (batch : stream.CodeBatch) (issued_bounds : issued.Bounded)
    (entry_bounds : CodeEntry.Bounds issued.env) (reachable : Stream.Batch.Reachable issued batch) :
    ∃ after, stream.CodeBatch.validate_all batch = .ok after ∧
      Stream.Batch.Reachable issued after :=
  WP.spec_imp_exists (stream.CodeBatch.validate_all.spec issued batch issued_bounds entry_bounds reachable)

/-- A bounded issued batch whose contents are independently valid runs from its seed to a
reachable state that `stream.CodeBatch.finish` accepts. -/
theorem stream.CodeBatch.validate_all.complete
    (issued : Stream.Batch.Issued)
    (entries : List Code) (issued_bounds : issued.Bounded)
    (entry_count : entries.length = issued.num_funcs.val)
    (typed : Module.Code.EntriesTyped issued.env issued.first_func.val entries)
    (signature_limits : CodeEntry.EnvironmentWithinLimits issued.env) (entry_bounds : CodeEntry.Bounds issued.env)
    (encoded : Rep (CodeEntry.CodeEncodingWithinLimits) entries issued.code.val) :
    ∃ after, stream.CodeBatch.validate_all issued.seed = .ok after ∧
      Stream.Batch.Reachable issued after ∧ stream.CodeBatch.finish after = .ok (.Ok ()) :=
  stream.CodeBatch.validate_all.complete_at_seed issued entries issued_bounds entry_count typed signature_limits
    entry_bounds encoded

/-- Finishing a reachable batch implies validation of every entry, in order, and consumption of
exactly its issued bytes. No premise prevalidates workers. -/
theorem stream.CodeBatch.finish.sound {issued : Stream.Batch.Issued}
    {batch : stream.CodeBatch}
    (reachable : Stream.Batch.Reachable issued batch) (entry_bounds : CodeEntry.Bounds issued.env)
    (finished : stream.CodeBatch.finish batch = .ok (.Ok ())) :
    ∃ entries, entries.length = issued.num_funcs.val ∧
      Binary.Rep (CodeEntry.CodeEncoding) entries issued.code.val ∧
      Module.Code.EntriesTyped issued.env issued.first_func.val entries :=
  Stream.Batch.Reachable.finished reachable entry_bounds finished

end Itasca
