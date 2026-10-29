import Itasca.Runtime.Interp.Relations.CopyRel
import Itasca.Runtime.Compiler.Local.Relations.Layout.ValueRegions

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem WordsAt.take {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (count : Nat) : WordsAt words base (bits.take count) := by
  apply WordsAt.append_left (right := bits.drop count)
  simpa only [List.take_append_drop] using h

theorem WordsAt.drop {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (count : Nat) (bound : count ≤ bits.length) :
    WordsAt words (base + count) (bits.drop count) := by
  have split : WordsAt words base (bits.take count ++ bits.drop count) := by
    simpa only [List.take_append_drop] using h
  simpa only [List.length_take, Nat.min_eq_left bound] using split.append_right

theorem WordsAt.region {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (offset width : Nat) (bound : offset ≤ bits.length) :
    WordsAt words (base + offset) ((bits.drop offset).take width) :=
  (h.drop offset bound).take width

theorem ValuesAt.lookup {words : List U64} {base : Nat} {values : List val}
    (h : ValuesAt words base values) {index : Nat} {value : val}
    (lookup : values[index]? = some value) :
    WordsAt words (base + Code.offset (values.map Code.valueType) index) (Code.encodeValue value) := by
  have bound : Code.offset (values.map Code.valueType) index ≤ (Code.encodeValues values).length := by
    rw [Code.encodeValues_length]
    exact Code.offset_le _ _
  have region := WordsAt.region h (Code.offset (values.map Code.valueType) index)
    (Code.width (Code.valueType value)) bound
  simpa only [Code.encodeValues_lookup lookup] using region

theorem WordsAt.set_outside {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (position : Nat) (value : U64)
    (outside : position < base ∨ base + bits.length ≤ position) :
    WordsAt (words.set position value) base bits := by
  apply h.congr_region (by simp only [List.length_set])
  intro j hj
  have different : position ≠ base + j := by omega
  simp only [List.getElem?_set, different, if_false]

/-- A newly written adjacent word extends the live prefix by one word. -/
theorem WordsAt.set_append {words : List U64} {base : Nat} {bits : List Nat}
    (h : WordsAt words base bits) (value : U64)
    (bound : base + bits.length < words.length) :
    WordsAt (words.set (base + bits.length) value) base (bits ++ [value.val]) := by
  apply WordsAt.append
  · exact h.set_outside _ value (Or.inr (by omega))
  · intro j hj
    have zero : j = 0 := by simp only [List.length_singleton] at hj; omega
    subst j
    refine ⟨by simpa only [List.length_set, Nat.add_zero] using bound, ?_⟩
    simp only [Nat.add_zero]
    rw [_root_.getElem!_pos (words.set (base + bits.length) value) (base + bits.length)
      (by simpa only [List.length_set] using bound), List.getElem_set_self]
    simp

/-- Replace a represented region by copying equally many words from a live
source. Prefix and suffix retain their original physical positions. -/
theorem WordsAt.copy_replace {words : List U64} {base src : Nat}
    {front old replacement back : List Nat}
    (live : WordsAt words base (front ++ old ++ back))
    (input : WordsAt words src replacement) (width : replacement.length = old.length)
    (order : base + front.length ≤ src ∨ src + replacement.length ≤ base + front.length)
    (source : src + replacement.length ≤ words.length)
    (destination : base + front.length + replacement.length ≤ words.length) :
    WordsAt (copyWords words (base + front.length) src replacement.length) base
      (front ++ replacement ++ back) := by
  have prefixRegion : WordsAt words base front := by
    apply WordsAt.append_left (right := old ++ back)
    simpa only [List.append_assoc] using live
  have suffix : WordsAt words (base + front.length + old.length) back := by
    have value : WordsAt words (base + front.length) (old ++ back) :=
      WordsAt.append_right (by simpa only [List.append_assoc] using live)
    exact value.append_right
  apply WordsAt.append
  · apply WordsAt.append
    · apply prefixRegion.copy_preserves (base + front.length) src replacement.length order source destination
      intro j hj
      exact Or.inl (by omega)
    · exact input.copy (base + front.length) order destination
  · have preserved := suffix.copy_preserves (base + front.length) src replacement.length order source destination
      (by intro j hj; exact Or.inr (by omega))
    simpa only [List.length_append, Nat.add_assoc, width] using preserved

end Itasca.Runtime.Interp
