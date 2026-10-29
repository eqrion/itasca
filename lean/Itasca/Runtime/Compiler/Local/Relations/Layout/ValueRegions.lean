import Itasca.Runtime.Representation.Encoding

/-! Local value boundaries in the mathematical word encoding. These lemmas
apply uniformly to one-word scalar/reference values and two-word vectors. -/
namespace Itasca.Runtime.Compiler

theorem encode_values_drop (values : List val) (count : Nat) :
    (encodeValues values).drop (offset (values.map valueType) count) =
      encodeValues (values.drop count) := by
  have hs := encode_values_append (values.take count) (values.drop count)
  rw [List.take_append_drop] at hs
  rw [hs]
  have hl : offset (values.map valueType) count = (encodeValues (values.take count)).length := by
    rw [encode_values_length]
    simp only [offset, List.map_take]
  rw [hl, List.drop_left]

theorem encode_values_lookup {values : List val} {index : Nat} {value : val}
    (lookup : values[index]? = some value) :
    ((encodeValues values).drop (offset (values.map valueType) index)).take
      (width (valueType value)) = encodeValue value := by
  rw [encode_values_drop]
  have bound : index < values.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have hv : values[index] = value := List.getElem?_eq_some_iff.mp lookup |>.2
  rw [List.drop_eq_getElem_cons bound, hv]
  change (encodeValue value ++ encodeValues (values.drop (index + 1))).take _ = _
  rw [← encode_value_length, List.take_left]

theorem encode_values_set {values : List val} {index : Nat} (bound : index < values.length)
    (replacement : val) :
    encodeValues (values.set index replacement) =
      (encodeValues values).take (offset (values.map valueType) index) ++
      encodeValue replacement ++
      (encodeValues values).drop (offset (values.map valueType) (index + 1)) := by
  rw [encode_values_take, encode_values_drop]
  rw [List.set_eq_take_append_cons_drop]
  simp only [bound, ↓reduceIte, encodeValues, List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Replacing a local with the same type preserves all local offsets. -/
theorem value_types_set {values : List val} {index : Nat} {old replacement : val}
    (lookup : values[index]? = some old) (typed : valueType replacement = valueType old) :
    (values.set index replacement).map valueType = values.map valueType := by
  rw [List.map_set, typed]
  have hm : (values.map valueType)[index]? = some (valueType old) := by
    simpa using congrArg (Option.map valueType) lookup
  have hb := (List.getElem?_eq_some_iff.mp hm).1
  have hv := (List.getElem?_eq_some_iff.mp hm).2
  rw [← hv]
  exact List.set_getElem_self hb

end Itasca.Runtime.Compiler
