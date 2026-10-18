import Exec.Spec.SimdIntegerArithmeticShape
namespace Exec.Spec.Simd
open SpecExt.Builtins

def arithmeticWords (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (integerArithmeticBits kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat)

theorem arithmetic_words_relation (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) :
    Forall₃ (fun result a b => IntegerArithmeticRel kind (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)) result)
      (arithmeticWords ty kind x y)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  have relation := integer_arithmetic_relation kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)
  cases ty <;> exact relation

theorem arithmetic_words_length (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) :
    (arithmeticWords ty kind x y).length = 128/lsize (lanetype_Jnn ty) := by
  simp [arithmeticWords]

theorem arithmetic_words_wf (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty word)) (arithmeticWords ty kind x y) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Exec.Spec.Simd
