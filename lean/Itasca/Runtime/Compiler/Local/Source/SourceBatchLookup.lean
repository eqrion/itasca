import Itasca.Runtime.Compiler.Local.Source.SourceSlice
import Itasca.Stream.Batch

/-!
Lookup of independently encoded entries and their batch source positions. The batch theorem transports the entry witness through source function ordering.
-/

/-! ## Source Entry Lookup -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Prefix-unique encodings identify an entry by the number of preceding
encoded entries, even when the complete byte list has a suffix. -/
theorem encoded_entry_lookup {α : Type} {R : α → List U8 → Prop}
    (unique : ModuleBinary.PrefixUnique R)
    {entries bytes prior first value second tail rest}
    (whole : ModuleBinary.Rep R entries bytes)
    (before : ModuleBinary.Rep R prior first) (item : R value second)
    (joined : bytes ++ tail = first ++ second ++ rest)
    (bound : prior.length < entries.length) : entries[prior.length]? = some value := by
  induction before generalizing entries bytes with
  | nil =>
    cases whole with
    | nil => simp at bound
    | @cons head entries headBytes following headEncoded followingEncoded =>
      obtain ⟨rfl, _, _⟩ := unique headEncoded item (by simpa [List.append_assoc] using joined)
      simp
  | @cons head prior headBytes following headEncoded followingEncoded ih =>
    cases whole with
    | nil => simp at bound
    | @cons actual entries actualBytes remaining actualEncoded remainingEncoded =>
      obtain ⟨rfl, rfl, suffix⟩ := unique actualEncoded headEncoded (by simpa [List.append_assoc] using joined)
      simpa using ih remainingEncoded (by simpa only [List.append_assoc] using suffix) (by simpa using bound)

/-- A successful entry's actual body is the code-list member at the exact
validated prior index. Framing equality, not a compiler premise, selects it. -/
theorem witness_source_lookup {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile)
    (types : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    {entries prior : List ModuleBinary.Code}
    (whole : ModuleBinary.Rep (Profile.CodeEncoding profile) entries data.val)
    (previous : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding profile)) data 0#usize prior start)
    (bound : prior.length < entries.length) :
    ∃ entry, entries[prior.length]? = some entry ∧ w.groups = entry.locals ∧
      Profile.BodyEncoding profile w.body entry.body := by
  have lookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  obtain ⟨ft, source, _, _, body, _⟩ := code.validate_body_with.profile_sound visitor w.body env w.ctx w.typeIdx profile w.ft
    w.startedState after lookup (witness_type_profile w types) w.body_accepted
  have actual := Profile.codeEncoding_of_parts w.header w.extent w.locals_bytes w.body_bytes body
  obtain ⟨first, prefixEncoding, prefixSpan⟩ := previous
  obtain ⟨last, lastEncoding, lastSpan⟩ := actual
  have joined : data.val ++ [] = first ++ last ++ data.val.drop finish.val := by
    have span := prefixSpan.suffix
    change data.val.drop 0 = first ++ data.val.drop start.val at span
    simp only [List.drop_zero] at span
    calc
      data.val ++ [] = data.val := List.append_nil _
      _ = first ++ data.val.drop start.val := span
      _ = first ++ last ++ data.val.drop finish.val := by rw [lastSpan.suffix, List.append_assoc]
  exact ⟨⟨w.groups, source⟩, encoded_entry_lookup (Profile.code_prefix_unique profile)
    whole prefixEncoding lastEncoding joined bound, rfl, body⟩

end Itasca.Runtime.Code

end

/-! ## Source Batch Lookup -/

section

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code

end
