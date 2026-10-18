import Exec.Spec.SimdCompareLists
import Exec.Spec.IntegerExtend
namespace Exec.Spec.Simd
open SpecExt.Builtins

def comparisonMasks (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) : List uN :=
  Map (fun answer => extend__ 1 (lsize (lanetype_Jnn ty)) .S (.mk_uN (proj_uN_0 answer)))
    (comparisonAnswers ty op x y)

theorem boolean_extend (width : Nat) (answer : Bool) :
    extend__ 1 width .S (.mk_uN (nat_of_bool answer)) =
      .mk_uN ((BitVec.ofNat 1 (nat_of_bool answer)).signExtend width).toNat := by
  have bounded : nat_of_bool answer < 2^1 := by cases answer <;> decide
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded] using
    extend_signed_bitvec 1 width (BitVec.ofNat 1 (nat_of_bool answer))

theorem comparison_masks_wf (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall (fun mask => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty mask))
      (comparisonMasks ty op x y) := by
  intro mask member
  obtain ⟨answer,answerMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp answerMember
  change wf_lane_ _ (.mk_lane__0 ty (extend__ 1 _ .S (.mk_uN (nat_of_bool _))))
  rw [boolean_extend]
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Exec.Spec.Simd
