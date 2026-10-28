import Itasca.Runtime.Code.Module.PreparedBatchSource
import Itasca.Runtime.Code.Module.SourceEntryPrepared

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

private def sourceOrdinal (env : module.Env) (index : Nat)
    (bounded : index < env.func_type_indices.val.length) : Usize :=
  Usize.ofNatCore index (by have cap := env.func_type_indices.property; scalar_tac)

/-- Independent entry encoding and typing construct the prepared source
sequence. The remaining assumptions bound only pure source preparation and
independently validated operand demand. -/
theorem PreparedBatchSource.of_encoded (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (bodyBytes localCount peak index : Nat) (start finish : Usize) (entries : List ModuleBinary.Code)
    (typed : ModuleCode.EntriesTyped (profile := profile) env index entries)
    (encoded : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncodingWithinLimits profile)) data start entries finish)
    (bounds : CodeEntry.Bounds env) (environment : Profile.Environment profile env)
    (limits : Profile.EnvironmentWithinLimits env)
    (maxima : ∀ (ordinal position next : Usize) (entry : ModuleBinary.Code),
      ModuleBinary.At (Profile.CodeEncodingWithinLimits profile) data position entry next →
      ∀ w : CodeEntry.Prepared data env ordinal position profile, w.finish = next →
      Profile.Body profile w.body env w.ctx.locals w.typeIdx →
      w.body.length ≤ bodyBytes ∧ w.ctx.locals.val.length ≤ localCount ∧
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands ≤ peak) :
    PreparedBatchSource data env profile bodyBytes localCount peak index start entries finish := by
  induction entries generalizing index start with
  | nil =>
    have same := encoded.rep_nil
    subst finish
    exact .nil index start
  | cons entry entries ih =>
    cases typed with
    | cons head rest =>
      obtain ⟨indexBound,entryTyped,_⟩ := head
      have fullTyped := Profile.EntryTyped.of_core entryTyped (environment.1 _ (List.getElem_mem _))
      let ordinal := sourceOrdinal env index indexBound
      have value : ordinal.val = index := rfl
      obtain ⟨next,entryBytes,remaining⟩ := encoded.rep_cons
      obtain ⟨w,ending,body⟩ := source_entry_prepared data env ordinal start next profile entry
        (by simpa only [value] using indexBound) (by simpa only [value] using fullTyped)
        bounds environment limits entryBytes
      obtain ⟨bytes,locals,operands⟩ := maxima ordinal start next entry entryBytes w ending body
      exact .cons ordinal value (by simpa only [value] using indexBound) (by simpa only [value] using fullTyped)
        entryBytes w ending bytes locals operands (ih (index+1) next rest remaining)

end Itasca.Runtime.Code
