import Itasca.Stream.BatchComplete

/-!
# Worker batches

Results for the `stream.CodeBatch` workers that `stream.validate_streaming` issues to the
scheduler. `validate_func` validates one entry, `validate_all` validates every remaining entry
with accepting callbacks, and `finish` checks that a worker validated every entry and consumed
its bytes.

Termination needs only a total visitor and the bounds of the issued environment. Completeness
assumes independently encoded and typed entries and an accepting visitor, never a worker assumed
to succeed. `stream.CodeBatch.finish.sound` holds for every worker reachable from an issued seed
through actual batch operations (`StreamBatch.Reachable`), whatever the scheduler did.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- `stream.CodeBatch.validate_func` returns an ordinary result, stores worker errors, and cannot
overflow its counter because a successful entry validation occurs only before the batch end. -/
theorem stream.CodeBatch.validate_func.total {V : Type}
    (visitor : code.OpVisitor V)
    (htotal : FullVisitor.Total visitor) (batch : stream.CodeBatch) (index : Usize) (v : V)
    (hbound : CodeEntry.Bounds batch.env)
    (hrange : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length) :
    ∃ r, stream.CodeBatch.validate_func visitor batch index v = .ok r :=
  stream.CodeBatch.validate_func.returns visitor htotal batch index v hbound hrange

/-- An accepting worker validates the independently encoded next entry and
advances exactly one function, without requiring prior dispatch. -/
theorem stream.CodeBatch.validate_func.complete {V : Type}
    (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (batch : stream.CodeBatch) (index : Usize)
    (entry : Code) (finish : Usize) (v : V)
    (herror : batch.error = none) (hcount : batch.num_validated.val < batch.num_funcs.val)
    (hindex : index.val = batch.first_func.val + batch.num_validated.val)
    (hi : index.val < batch.env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed batch.env batch.env.func_type_indices.val[index.val] entry)
    (hlimits : Profile.EnvironmentWithinLimits batch.env) (hbound : CodeEntry.Bounds batch.env)
    (hbytes : At (Profile.CodeEncodingWithinLimits) batch.code batch.validated_end entry finish) :
    ∃ count v', count.val = batch.num_validated.val + 1 ∧
      stream.CodeBatch.validate_func visitor batch index v = .ok (.Ok (),
        { batch with num_validated := count, validated_end := finish }, v') :=
  stream.CodeBatch.validate_func.complete_at visitor haccept batch index entry finish v herror
    hcount hindex hi htyped hlimits hbound hbytes

/-- Running `stream.CodeBatch.validate_all` terminates in a reachable state, including on invalid
bytes and stored errors. -/
theorem stream.CodeBatch.validate_all.spec
    (issued : StreamBatch.Issued)
    (batch : stream.CodeBatch) (hissued : issued.Bounded)
    (hbound : CodeEntry.Bounds issued.env) (hreach : StreamBatch.Reachable issued batch) :
    stream.CodeBatch.validate_all batch ⦃ after => StreamBatch.Reachable issued after ⦄ :=
  stream.CodeBatch.validate_all.reachable issued batch hissued hbound hreach

/-- `stream.CodeBatch.validate_all` returns a reachable batch. -/
theorem stream.CodeBatch.validate_all.total
    (issued : StreamBatch.Issued)
    (batch : stream.CodeBatch) (hissued : issued.Bounded)
    (hbound : CodeEntry.Bounds issued.env) (hreach : StreamBatch.Reachable issued batch) :
    ∃ after, stream.CodeBatch.validate_all batch = .ok after ∧
      StreamBatch.Reachable issued after :=
  WP.spec_imp_exists (stream.CodeBatch.validate_all.spec issued batch hissued hbound hreach)

/-- Independently encoded and typed batch contents are accepted by running the extracted worker
loop, which ends with every function validated and `error = none`. -/
theorem stream.CodeBatch.validate_all.complete
    (batch : stream.CodeBatch)
    (entries : List Code) (finish : Usize)
    (herror : batch.error = none)
    (hcount : batch.num_validated.val + entries.length = batch.num_funcs.val)
    (htyped : ModuleCode.EntriesTyped batch.env
      (batch.first_func.val + batch.num_validated.val) entries)
    (hlimits : Profile.EnvironmentWithinLimits batch.env) (hbound : CodeEntry.Bounds batch.env)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits)) batch.code batch.validated_end entries finish) :
    stream.CodeBatch.validate_all batch = .ok
      { batch with num_validated := batch.num_funcs, validated_end := finish, error := none } :=
  stream.CodeBatch.validate_all.complete_at batch entries finish herror hcount htyped hlimits
    hbound hbytes

/-- A bounded issued batch whose contents are independently valid runs from its seed to a
reachable state that `stream.CodeBatch.finish` accepts. -/
theorem stream.CodeBatch.validate_all.complete_seed
    (issued : StreamBatch.Issued)
    (entries : List Code) (hissued : issued.Bounded)
    (hcount : entries.length = issued.num_funcs.val)
    (htyped : ModuleCode.EntriesTyped issued.env issued.first_func.val entries)
    (hlimits : Profile.EnvironmentWithinLimits issued.env) (hbound : CodeEntry.Bounds issued.env)
    (hbytes : Rep (Profile.CodeEncodingWithinLimits) entries issued.code.val) :
    ∃ after, stream.CodeBatch.validate_all issued.seed = .ok after ∧
      StreamBatch.Reachable issued after ∧ stream.CodeBatch.finish after = .ok (.Ok ()) :=
  stream.CodeBatch.validate_all.complete_at_seed issued entries hissued hcount htyped hlimits
    hbound hbytes

/-- Finishing a reachable batch implies validation of every entry, in order, and consumption of
exactly its issued bytes. No premise prevalidates workers. -/
theorem stream.CodeBatch.finish.sound {issued : StreamBatch.Issued}
    {batch : stream.CodeBatch}
    (h : StreamBatch.Reachable issued batch) (hbound : CodeEntry.Bounds issued.env)

    (hfinish : stream.CodeBatch.finish batch = .ok (.Ok ())) :
    ∃ entries, entries.length = issued.num_funcs.val ∧
      ModuleBinary.Rep (Profile.CodeEncoding) entries issued.code.val ∧
      ModuleCode.EntriesTyped issued.env issued.first_func.val entries :=
  StreamBatch.Reachable.finished h hbound hfinish

end Itasca
