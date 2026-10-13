import Itasca.Binary.Wasm1.PrefixUnique
import Itasca.Handler.BrTableComplete

open Aeneas Aeneas.Std

namespace Itasca

theorem Leb128.Decoded.unique {data start x y next last}
    (hx : Leb128.Decoded data start x next) (hy : Leb128.Decoded data start y last) :
    x = y ∧ next = last := by
  have h := (reader.read_u32_leb.complete data start x next hx).symm.trans
    (reader.read_u32_leb.complete data start y last hy)
  simpa using h

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

theorem Immediate.unique {data start opcode t u bs cs next last}
    (ht : Immediate opcode t bs) (hu : Immediate opcode u cs)
    (hb : BytesAt data start bs next) (hc : BytesAt data start cs last) :
    t = u ∧ next = last := by
  obtain ⟨rfl, rfl, _⟩ := Immediate.prefix_unique opcode ht hu (hb.suffix.symm.trans hc.suffix)
  exact ⟨rfl, UScalar.eq_of_val_eq (hb.length.trans hc.length.symm)⟩

/-- The independent binary relation determines both its token and end cursor. -/
theorem At.unique {data start t u next last}
    (ht : At data start t next) (hu : At data start u last) : t = u ∧ next = last := by
  obtain ⟨bs, ht, hb⟩ := ht
  obtain ⟨cs, hu, hc⟩ := hu
  obtain ⟨rfl, rfl, _⟩ := token_prefix_unique ht hu (hb.suffix.symm.trans hc.suffix)
  exact ⟨rfl, UScalar.eq_of_val_eq (hb.length.trans hc.length.symm)⟩

theorem Consumed.nil_of_equal_cursor {data start tokens next}
    (h : Consumed data start tokens next) (hp : start = next) : tokens = [] := by
  cases h with
  | nil => rfl
  | snoc hs ht => have := hs.span; have := ht.span; subst next; omega

/-- Two complete parses of the same byte interval have the same flat tokens. -/
theorem Consumed.unique {data start xs ys next}
    (hx : Consumed data start xs next) (hy : Consumed data start ys next) : xs = ys := by
  induction xs generalizing start ys with
  | nil =>
      have hn := hx.empty_eq rfl
      exact (hy.nil_of_equal_cursor hn.symm).symm
  | cons x xs ih =>
      obtain ⟨p, hp, hxs⟩ := Consumed.cons_iff.mp hx
      cases ys with
      | nil =>
          have hn := hy.empty_eq rfl
          have := hp.span
          have := hxs.span
          subst next
          omega
      | cons y ys =>
          obtain ⟨q, hq, hys⟩ := Consumed.cons_iff.mp hy
          obtain ⟨rfl, rfl⟩ := hp.unique hq
          rw [ih hxs hys]

/-- Complete body bytes determine one structured tree, regardless of typing. -/
theorem BodyEncoding.unique {data xs ys}
    (hx : BodyEncoding data xs) (hy : BodyEncoding data ys) : xs = ys := by
  obtain ⟨xt, xp, hx, hxp, hxs⟩ := hx
  obtain ⟨yt, yp, hy, hyp, hys⟩ := hy
  have hp : xp = yp := UScalar.eq_of_val_eq (hxp.trans hyp.symm)
  subst yp
  have ht := hx.unique hy
  subst yt
  exact hxs.unique hys

end Itasca.Wasm1
