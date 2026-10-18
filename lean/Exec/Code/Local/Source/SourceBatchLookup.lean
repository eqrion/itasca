import Exec.Code.Local.Source.SourceEntryLookup
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The reachable worker's validated prefix identifies its next exact entry
inside the independently encoded issued code view. -/
theorem witness_batch_source_lookup {V : Type} {visitor : code.OpVisitor V}
    {issued : StreamBatch.Issued} {batch : stream.CodeBatch}
    {index finish before after}
    (w : CodeEntry.Witness visitor batch.code batch.env index batch.validated_end finish before after batch.profile)
    (reachable : StreamBatch.Reachable issued batch)
    (bounds : CodeEntry.Bounds batch.env)
    (types : ∀ ft ∈ batch.env.types.val, Profile.FuncType batch.profile ft)
    {entries : List ModuleBinary.Code}
    (whole : ModuleBinary.Rep (Profile.CodeEncoding issued.profile) entries issued.code.val)
    (count : batch.num_validated.val < entries.length) :
    ∃ entry, entries[batch.num_validated.val]? = some entry ∧ w.groups = entry.locals ∧
      Profile.BodyEncoding batch.profile w.body entry.body := by
  obtain ⟨identity, previous, _⟩ := reachable.validation
  obtain ⟨_, _, envEq, codeEq, _, _, _, profileEq⟩ := identity
  have bound : CodeEntry.Bounds issued.env := by simpa only [envEq] using bounds
  have signatures : ∀ ft ∈ issued.env.types.val, Profile.FuncType batch.profile ft := by simpa only [envEq] using types
  obtain ⟨prior, length, encoded, _⟩ := previous.typed bound signatures profileEq.symm
  have priorBytes : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding batch.profile))
      batch.code 0#usize prior batch.validated_end := by simpa only [codeEq] using encoded
  have complete : ModuleBinary.Rep (Profile.CodeEncoding batch.profile) entries batch.code.val := by
    simpa only [profileEq, codeEq] using whole
  obtain ⟨entry, found, groups, body⟩ := witness_source_lookup w types complete priorBytes (by omega)
  exact ⟨entry, by simpa only [length] using found, groups, body⟩

/-- The code-view ordinal is translated to the complete decoded code list by
its exact preceding source entries. -/
theorem source_entry_offset {prior entries remaining : List ModuleBinary.Code} {index entry}
    (found : entries[index]? = some entry) :
    (prior ++ entries ++ remaining)[prior.length + index]? = some entry := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem sourceFunctions_lookup {raw : ModuleBinary.Module} {index : Nat} {typeIndex entry}
    (typeFound : raw.functions[index]? = some typeIndex)
    (codeFound : raw.codes[index]? = some entry) :
    (sourceFunctions raw)[index]? = some (sourceFunctionCode typeIndex entry) := by
  have typeBound := (List.getElem?_eq_some_iff.mp typeFound).1
  have codeBound := (List.getElem?_eq_some_iff.mp codeFound).1
  have bound : index < (sourceFunctions raw).length := by simp [sourceFunctions]; omega
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨bound, ?_⟩
  simp only [sourceFunctions, List.getElem_zipWith]
  rw [(List.getElem?_eq_some_iff.mp typeFound).2, (List.getElem?_eq_some_iff.mp codeFound).2]

end Exec.Code
