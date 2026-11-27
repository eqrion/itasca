import WebAssembly.Binary.Leb128

namespace WebAssembly.Binary.Leb128

theorem continuation_prefix_le (byte : α → Nat) (xs ys : List α) (a : α) (leftTail bs : List α)
    (hx : ∀ b ∈ xs, 128 ≤ byte b) (hy : ∀ b ∈ ys, 128 ≤ byte b)
    (ha : byte a < 128) (heq : xs ++ a :: leftTail = ys ++ bs) :
    ys.length ≤ xs.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have hay : a = y := (List.cons.inj heq).1
      have := hy y (by simp)
      subst y
      omega
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := List.cons.inj heq
      have hxs : ∀ b ∈ xs, 128 ≤ byte b := by intros b hb; exact hx b (by simp [hb])
      have hys : ∀ b ∈ ys, 128 ≤ byte b := by intros b hb; exact hy b (by simp [hb])
      simpa using ih ys hxs hys htail

theorem terminated_unique (byte : α → Nat) (xs ys : List α) (a b : α) (leftTail rightTail : List α)
    (hx : ∀ c ∈ xs, 128 ≤ byte c) (hy : ∀ c ∈ ys, 128 ≤ byte c)
    (ha : byte a < 128) (hb : byte b < 128)
    (heq : xs ++ a :: leftTail = ys ++ b :: rightTail) : xs = ys ∧ a = b := by
  have hxy := continuation_prefix_le byte xs ys a leftTail (b :: rightTail) hx hy ha heq
  have hyx := continuation_prefix_le byte ys xs b rightTail (a :: leftTail) hy hx hb heq.symm
  have hlen : xs.length = ys.length := by omega
  have hfirst : xs = ys := by
    have := congrArg (List.take xs.length) heq
    simpa [List.take_append, hlen] using this
  subst ys
  exact ⟨rfl, (List.cons.inj (List.append_cancel_left heq)).1⟩

/-- Two encodings that are prefixes of the same byte string are equal and have equal values. -/
theorem SignedForm.prefix_unique {byte : α → Nat} {payload : List α → Nat} {terminal : Int → Int → α → Int}
    {n : Nat} {lo hi : Int} {xs ys : List α} {x y : Int} {leftTail rightTail : List α}
    (hx : SignedForm byte payload terminal n lo hi xs x) (hy : SignedForm byte payload terminal n lo hi ys y) (heq : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y := by
  rcases hx with ⟨xs', a, rfl, _, hxmore, ha, rfl, _⟩
  rcases hy with ⟨ys', b, rfl, _, hymore, hb, rfl, _⟩
  simp only [List.append_assoc, List.singleton_append] at heq
  obtain ⟨rfl, rfl⟩ := terminated_unique byte xs' ys' a b leftTail rightTail hxmore hymore ha hb heq
  exact ⟨rfl, rfl⟩

theorem UnsignedForm.prefix_unique {byte : α → Nat} {payload : List α → Nat}
    {xs ys rest tail : List α} {x y : Nat} (hx : UnsignedForm byte payload xs x)
    (hy : UnsignedForm byte payload ys y) (he : xs ++ rest = ys ++ tail) :
    xs = ys ∧ x = y := by
  obtain ⟨xs, a, rfl, _, hx, ha, _, rfl⟩ := hx
  obtain ⟨ys, b, rfl, _, hy, hb, _, rfl⟩ := hy
  simp only [List.append_assoc, List.singleton_append] at he
  obtain ⟨rfl, rfl⟩ := terminated_unique byte xs ys a b rest tail hx hy ha hb he
  exact ⟨rfl, rfl⟩

end WebAssembly.Binary.Leb128
