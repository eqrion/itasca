import Itasca.Binary.Module

/-!
# Prefix uniqueness of the binary grammar

Defines `PrefixUnique` and `Unique` for byte-level relations and shows that they are preserved by
sequences (`PrefixUnique.rep`, `PrefixUnique.rep_unique`) and vectors (`PrefixUnique.vec`). Proves
`PrefixUnique` for the primitive encodings: LEB128 integers, indices, bytes, names and float bits.
Prefix uniqueness is what makes concatenated encodings decode in only one way.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- An encoding relation determines both the value and the consumed prefix of any byte string that
starts with an encoding. Suffixes are arbitrary lists, with no implementation bound. -/
def PrefixUnique {α : Type} (R : α → List U8 → Prop) : Prop :=
  ∀ ⦃x y first second rest tail⦄, R x first → R y second →
    first ++ rest = second ++ tail → x = y ∧ first = second ∧ rest = tail

/-- An encoding relation determines its value from the complete byte string. -/
def Unique {α : Type} (R : α → List U8 → Prop) : Prop :=
  ∀ ⦃x y bytes⦄, R x bytes → R y bytes → x = y

/-- Prefix uniqueness implies uniqueness. -/
theorem PrefixUnique.unique {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) : Unique R := by
  intro x y bytes hx hy
  exact (h hx hy (rest := []) (tail := []) rfl).1

/-- Equal-length prefixes of equal lists are equal, and so are the remainders. -/
theorem split_of_length {α : Type} {xs ys rest tail : List α}
    (he : xs ++ rest = ys ++ tail) (hl : xs.length = ys.length) :
    xs = ys ∧ rest = tail := by
  have h := congrArg (List.take xs.length) he
  have hx : xs = ys := by simpa [List.take_append, hl] using h
  subst ys
  exact ⟨rfl, List.append_cancel_left he⟩

/-- Prefix uniqueness extends to sequences of the same length. -/
theorem PrefixUnique.rep {α : Type} {R : α → List U8 → Prop} (h : PrefixUnique R)
    {xs ys first second rest tail} (hx : Rep R xs first) (hy : Rep R ys second)
    (hl : xs.length = ys.length) (he : first ++ rest = second ++ tail) :
    xs = ys ∧ first = second ∧ rest = tail := by
  induction hx generalizing ys second with
  | nil =>
    cases hy with
    | nil => exact ⟨rfl, rfl, he⟩
    | cons => simp at hl
  | @cons x xs a b ha hb ih =>
    cases hy with
    | nil => simp at hl
    | @cons y ys c d hc hd =>
      obtain ⟨rfl, rfl, ht⟩ := h ha hc (by simpa [List.append_assoc] using he)
      obtain ⟨rfl, rfl, rfl⟩ := ih hd (by simpa using hl) ht
      exact ⟨rfl, rfl, rfl⟩

/-- A prefix-unique relation with nonempty encodings gives unique sequence encodings. -/
theorem PrefixUnique.rep_unique {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) (hn : ∀ x bs, R x bs → bs ≠ []) : Unique (Rep R) := by
  intro xs ys bytes hx hy
  generalize he : bytes = other at hy
  induction hx generalizing ys other with
  | nil =>
    cases hy with
    | nil => rfl
    | @cons y ys a b ha hb =>
      exact False.elim (hn y a ha (List.append_eq_nil_iff.mp he.symm).1)
  | @cons x xs a b ha hb ih =>
    cases hy with
    | nil =>
      exact False.elim (hn x a ha (List.append_eq_nil_iff.mp he).1)
    | @cons y ys c d hc hd =>
      obtain ⟨rfl, rfl, rfl⟩ := h ha hc he
      exact congrArg (List.cons x) (ih b rfl hd)

/-- Unsigned LEB128 encodings are prefix-unique. -/
theorem leb_prefix_unique : PrefixUnique (fun n bs => Leb128.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Leb128.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

/-- Index encodings are prefix-unique. -/
theorem index_prefix_unique : PrefixUnique IndexEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨hv, rfl, ht⟩ := leb_prefix_unique hx hy he
  exact ⟨UScalar.eq_of_val_eq hv, rfl, ht⟩

/-- Vector encodings of a prefix-unique relation are prefix-unique. -/
theorem PrefixUnique.vec {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) : PrefixUnique (VecEncoding R) := by
  intro xs ys a b rest tail hx hy he
  obtain ⟨n, entries, hn, hx, rfl⟩ := hx
  obtain ⟨m, entries', hm, hy, rfl⟩ := hy
  obtain ⟨hl, rfl, ht⟩ := leb_prefix_unique hn hm (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := h.rep hx hy hl ht
  exact ⟨rfl, rfl, rfl⟩

/-- Raw byte encodings are prefix-unique. -/
theorem byte_prefix_unique : PrefixUnique ByteEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  exact ⟨rfl, rfl, rfl⟩

/-- Name encodings are prefix-unique. -/
theorem name_prefix_unique : PrefixUnique NameEncoding := by
  intro x y a b rest tail hx hy he
  exact byte_prefix_unique.vec hx.1 hy.1 he

/-- Fixed-width float bit pattern encodings are prefix-unique. -/
theorem float_prefix_unique (n : Nat) :
    PrefixUnique (fun bits bs => FloatBits.Encoding n bs bits) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := split_of_length he (hx.1.trans hy.1.symm)
  exact ⟨hx.2.trans hy.2.symm, rfl, rfl⟩

/-- Signed 32-bit LEB128 encodings are prefix-unique. -/
theorem signed32_prefix_unique : PrefixUnique (fun n bs => SignedLeb32.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := SignedLeb32.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

/-- Signed 64-bit LEB128 encodings are prefix-unique. -/
theorem signed64_prefix_unique : PrefixUnique (fun n bs => SignedLeb64.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := SignedLeb64.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

end Itasca.ModuleBinary
