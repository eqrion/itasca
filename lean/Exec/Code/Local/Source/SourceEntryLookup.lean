import Exec.Code.Local.Source.SourceSlice
import Itasca.Stream.Batch
namespace Exec.Code
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

end Exec.Code
