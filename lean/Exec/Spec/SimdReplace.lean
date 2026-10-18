import Exec.Spec.SimdShape
namespace Exec.Spec.Simd
open SpecExt.Builtins

theorem index_wf (ty : lanetype) (index : Nat) (valid : index < 128/lsize ty) :
    wf_uN 8 (.mk_uN index) := by
  apply unsigned_wf_of_lt
  have bound : 128/lsize ty ≤ 16 := by cases ty <;> decide
  omega

theorem replace_step (ty : lanetype) (index : Nat) (before result : BitVec 128) (input : BitVec 64)
    (valid : index < 128/lsize ty)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf ty)
      ((lanes_ (shapeOf ty) (.mk_uN before.toNat)).set index
        (laneOfBits ty (input.setWidth (lsize ty)).toNat))) :
    Step_pure [.VCONST .V128 (.mk_uN before.toNat), .CONST (unpack ty) (scalarInput ty input),
      .VREPLACE_LANE (shapeOf ty) (.mk_uN index)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vreplace_lane _ ty (scalarInput ty input) (128/lsize ty) (.mk_uN index) _
    (some (laneOfBits ty (input.setWidth (lsize ty)).toNat))
  · exact pack_scalarInput ty input
  · simp
  · simpa only [List.modify_eq_set, proj_uN_0, Option.get!, shapeOf] using packed
  · exact const_wf before
  · exact .admininstr_case_13 _ _ (scalarInput_wf ty input)
  · exact .admininstr_case_35 _ _ (shapeOf_wf ty) (index_wf ty index valid)
  · exact const_wf result
  · exact shapeOf_wf ty

end Exec.Spec.Simd
