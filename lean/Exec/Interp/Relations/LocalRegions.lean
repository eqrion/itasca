import Exec.Interp.Relations.Regions

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A same-type local replacement changes exactly that local's encoded region.
The remaining local values and the operand stack retain their word addresses. -/
theorem ValuesAt.copy_local {words : List U64} {base src index : Nat}
    {locals stack : List val} {old replacement : val}
    (live : ValuesAt words base (locals ++ stack))
    (lookup : locals[index]? = some old)
    (typed : Code.valueType replacement = Code.valueType old)
    (input : WordsAt words src (Code.encodeValue replacement))
    (order : base + Code.offset (locals.map Code.valueType) index ≤ src ∨
      src + (Code.encodeValue replacement).length ≤ base + Code.offset (locals.map Code.valueType) index)
    (source : src + (Code.encodeValue replacement).length ≤ words.length)
    (destination : base + Code.offset (locals.map Code.valueType) index +
      (Code.encodeValue replacement).length ≤ words.length) :
    ValuesAt (copyWords words (base + Code.offset (locals.map Code.valueType) index)
      src (Code.encodeValue replacement).length) base (locals.set index replacement ++ stack) := by
  have bound : index < locals.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have oldEq : locals[index] = old := List.getElem?_eq_some_iff.mp lookup |>.2
  have self : locals.set index old = locals := by
    rw [← oldEq]
    exact List.set_getElem_self bound
  have split := Code.encodeValues_set bound old
  rw [self] at split
  have offsetBound : Code.offset (locals.map Code.valueType) index ≤ (Code.encodeValues locals).length := by
    rw [Code.encodeValues_length]
    exact Code.offset_le _ _
  have length : ((Code.encodeValues locals).take (Code.offset (locals.map Code.valueType) index)).length =
      Code.offset (locals.map Code.valueType) index := by
    simp only [List.length_take, Nat.min_eq_left offsetBound]
  have region : WordsAt words base
      ((Code.encodeValues locals).take (Code.offset (locals.map Code.valueType) index) ++
      Code.encodeValue old ++
      ((Code.encodeValues locals).drop (Code.offset (locals.map Code.valueType) (index + 1)) ++ Code.encodeValues stack)) := by
    have full : WordsAt words base (Code.encodeValues locals ++ Code.encodeValues stack) := by
      simpa only [ValuesAt, Code.encodeValues_append] using live
    rw [split] at full
    simpa only [List.append_assoc] using full
  have widths : (Code.encodeValue replacement).length = (Code.encodeValue old).length := by
    simp only [Code.encodeValue_length, typed]
  have changed := WordsAt.copy_replace region input widths
    (by simpa only [length] using order)
    source (by simpa only [length] using destination)
  rw [length] at changed
  have updated := Code.encodeValues_set bound replacement
  simp only [ValuesAt, Code.encodeValues_append, updated]
  simpa only [List.append_assoc] using changed

end Itasca.Runtime.Interp
