import Itasca.Runtime.Spec.Simd.ByteView

/-!
Byte-lane selection and list-index transport.

Main declarations: `byteLanes_integer` and `byteWords_append_get`. A direct consumer is `Spec.Simd.Swizzle`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem byteLanes_integer (bits : BitVec 128) :
    Forall (fun lane => proj_lane__0 lane ≠ none) (lanes_ (shapeOf .I8) (.mk_uN bits.toNat)) := by
  rw [←byteWords_lanes]
  intro lane member
  obtain ⟨word,_,rfl⟩ := List.mem_map.mp member
  simp [proj_lane__0]

theorem byteLanes_unwrap (bits : BitVec 128) :
    Map (fun lane => Option.get! (proj_lane__0 lane))
      (lanes_ (shapeOf .I8) (.mk_uN bits.toNat)) = byteWords bits := by
  rw [←byteWords_lanes]
  simp [Map,List.map_map,Function.comp_def,proj_lane__0]

theorem byteLanes_get (bits : BitVec 128) (index : Nat) (valid : index < 16) :
    (lanes_ (shapeOf .I8) (.mk_uN bits.toNat))[index]! =
      .mk_lane__0 .I8 (.mk_uN (byteAt bits index)) := by
  exact lanes_get .I8 bits index valid

theorem byteWords_append_get (x y : BitVec 128) (index : Nat) (valid : index < 32) :
    (byteWords x ++ byteWords y)[index]! =
      if index < 16 then .mk_uN (byteAt x index) else .mk_uN (byteAt y (index-16)) := by
  by_cases first : index < 16
  · simp only [if_pos first]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_append,byteWords,first]
  · simp only [if_neg first]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_append,byteWords,first,show index-16 < 16 by omega]

end Itasca.Runtime.Spec.Simd
