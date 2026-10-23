import Itasca.Binary.Wasm1.PrefixUnique
import Itasca.Binary.Wasm1.EncodingComplete

/-!
# Uniqueness of Wasm 1.0 decoding at a cursor

Shows that LEB128 indices and `br_table` label vectors determine their decoded values
(`Leb128.Decoded.unique`, `BrTable.LabelsDecoded.unique`, `BrTable.Decoded.unique`).
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A decoded unsigned LEB128 value and cursor are determined by the start. -/
theorem Leb128.Decoded.unique {data start x y next last}
    (hx : Leb128.Decoded data start x next) (hy : Leb128.Decoded data start y last) :
    x = y ∧ next = last :=
  Leb128.Decoded.deterministic data start x y next last hx hy

/-- A label run of known length is determined by the start. -/
theorem BrTable.LabelsDecoded.unique {data start xs ys next last}
    (hx : BrTable.LabelsDecoded data start xs next)
    (hy : BrTable.LabelsDecoded data start ys last) (hlen : xs.length = ys.length) :
    xs = ys ∧ next = last := by
  have empty : ∀ {p q}, BrTable.LabelsDecoded data p [] q → q = p := by
    intro p q h
    generalize he : [] = zs at h
    cases h with
    | nil => rfl
    | snoc => simp at he
  induction xs generalizing start ys with
  | nil =>
      have he : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst ys
      exact ⟨rfl, (empty hx).trans (empty hy).symm⟩
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          obtain ⟨p, hxp, hxs⟩ := BrTable.LabelsDecoded.cons_iff.mp hx
          obtain ⟨q, hyq, hys⟩ := BrTable.LabelsDecoded.cons_iff.mp hy
          obtain ⟨rfl, rfl⟩ := hxp.unique hyq
          obtain ⟨rfl, rfl⟩ := ih hxs hys (by simpa using hlen)
          exact ⟨rfl, rfl⟩

/-- A decoded `br_table` immediate is determined by the start. -/
theorem BrTable.Decoded.unique {data start xs ys x y next last}
    (hx : BrTable.Decoded data start xs x next) (hy : BrTable.Decoded data start ys y last) :
    xs = ys ∧ x = y ∧ next = last := by
  obtain ⟨n, p, q, hn, hlen, hs, ht⟩ := hx
  obtain ⟨m, r, s, hm, hlen', hs', ht'⟩ := hy
  obtain ⟨rfl, rfl⟩ := hn.unique hm
  obtain ⟨rfl, rfl⟩ := hs.unique hs' (hlen.trans hlen'.symm)
  exact ⟨rfl, ht.unique ht'⟩

end Itasca

namespace Itasca.Wasm1

end Itasca.Wasm1
