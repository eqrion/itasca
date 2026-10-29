import Itasca.Runtime.Spec.Simd.Replace
import SpecExt.Builtins.LaneLaws

/-!
Scalar output types and signedness for lane extraction.

Main declarations: `scalarOutput` and `extractSign`. A direct consumer is `Spec.Simd.ByteView`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def scalarOutput (ty : lanetype) (bits : Nat) : num_ :=
  match ty with
  | .I8 | .I16 | .I32 => .mk_num__0 .I32 (.mk_uN bits)
  | .I64 => .mk_num__0 .I64 (.mk_uN bits)
  | .F32 => .mk_num__1 .F32 (floatOfBits 32 bits)
  | .F64 => .mk_num__1 .F64 (floatOfBits 64 bits)

theorem scalarOutput_wf (ty : lanetype) (bits : Nat) (bound : bits < 2^lsize ty) :
    wf_num_ (unpack ty) (scalarOutput ty bits) := by
  cases ty with
  | I8 =>
    apply unsigned_num_wf .I32
    change bits < 2^8 at bound
    change bits < 2^32
    omega
  | I16 =>
    apply unsigned_num_wf .I32
    change bits < 2^16 at bound
    change bits < 2^32
    omega
  | I32 => exact unsigned_num_wf .I32 _ bound
  | I64 => exact unsigned_num_wf .I64 _ bound
  | F32 => exact float_num_wf .F32 _ (floatOfBits_wf_32 _ bound)
  | F64 => exact float_num_wf .F64 _ (floatOfBits_wf_64 _ bound)

theorem unpack_laneOfBits (ty : lanetype) (bits : Nat) (bound : bits < 2^lsize ty) :
    fun_unpacknum_ ty (laneOfBits ty bits) (some (scalarOutput ty bits)) := by
  have wf := scalarOutput_wf ty bits bound
  cases ty with
  | I32 => exact .fun_unpacknum__case_0 _ wf
  | I64 => exact .fun_unpacknum__case_1 _ wf
  | F32 => exact .fun_unpacknum__case_2 _ wf
  | F64 => exact .fun_unpacknum__case_3 _ wf
  | I8 => exact .fun_unpacknum__case_4 _ (by decide) wf
  | I16 => exact .fun_unpacknum__case_5 _ (by decide) wf

theorem lanes_get (ty : lanetype) (v : BitVec 128) (index : Nat)
    (valid : index < 128/lsize ty) :
    (lanes_ (shapeOf ty) (.mk_uN v.toNat))[index]! =
      laneOfBits ty (v.toNat/2^(lsize ty*index)%2^lsize ty) := by
  change (unpackLanes ty (128/lsize ty) v.toNat)[index]! = _
  rw [List.getElem!_eq_getElem?_getD, unpackLanes_getElem?, if_pos valid, Option.getD_some]

def extractSign (ty : lanetype) : Option sx :=
  match ty with
  | .I8 | .I16 => some .U
  | _ => none

theorem extract_wf (ty : lanetype) (index : Nat) (valid : index < 128/lsize ty) :
    wf_admininstr (.VEXTRACT_LANE (shapeOf ty) (extractSign ty) (.mk_uN index)) := by
  apply wf_admininstr.admininstr_case_34 _ _ _ (shapeOf_wf ty) (index_wf ty index valid) (by decide)
  cases ty <;> decide

theorem extract_num_step (nt : numtype) (index : Nat) (v : BitVec 128)
    (valid : index < 128/lsize (lanetype_numtype nt)) :
    Step_pure [.VCONST .V128 (.mk_uN v.toNat),
      .VEXTRACT_LANE (shapeOf (lanetype_numtype nt)) none (.mk_uN index)]
      [.CONST nt (scalarOutput (lanetype_numtype nt)
        (v.toNat/2^(lsize (lanetype_numtype nt)*index)%2^lsize (lanetype_numtype nt)))] := by
  have wf := scalarOutput_wf (lanetype_numtype nt)
    (v.toNat/2^(lsize (lanetype_numtype nt)*index)%2^lsize (lanetype_numtype nt))
    (Nat.mod_lt _ (by positivity))
  apply Step_pure.vextract_lane_num _ nt (128/lsize (lanetype_numtype nt)) (.mk_uN index) _
    (some (scalarOutput (lanetype_numtype nt)
      (v.toNat/2^(lsize (lanetype_numtype nt)*index)%2^lsize (lanetype_numtype nt))))
  · simpa only [lanes_, proj_uN_0, unpackLanes_length] using valid
  · change fun_unpacknum_ _ (lanes_ (shapeOf (lanetype_numtype nt)) (.mk_uN v.toNat))[index]! _
    rw [lanes_get _ _ _ valid]
    exact unpack_laneOfBits _ _ (Nat.mod_lt _ (by positivity))
  · simp
  · rfl
  · exact const_wf v
  · have result := extract_wf (lanetype_numtype nt) index valid
    cases nt <;> exact result
  · apply wf_admininstr.admininstr_case_13
    cases nt <;> exact wf
  · exact shapeOf_wf _

theorem extract_pack_step (pt : packtype) (index : Nat) (v : BitVec 128)
    (valid : index < 128/lsize (lanetype_packtype pt)) :
    Step_pure [.VCONST .V128 (.mk_uN v.toNat),
      .VEXTRACT_LANE (shapeOf (lanetype_packtype pt)) (some .U) (.mk_uN index)]
      [.CONST .I32 (scalarOutput (lanetype_packtype pt)
        (v.toNat/2^(lsize (lanetype_packtype pt)*index)%2^lsize (lanetype_packtype pt)))] := by
  have wf := scalarOutput_wf (lanetype_packtype pt)
    (v.toNat/2^(lsize (lanetype_packtype pt)*index)%2^lsize (lanetype_packtype pt))
    (Nat.mod_lt _ (by positivity))
  apply Step_pure.vextract_lane_pack _ pt (128/lsize (lanetype_packtype pt)) .U (.mk_uN index)
  · cases pt <;> simp [scalarOutput, lanetype_packtype, proj_num__0]
  · change proj_lane__0 (lanes_ (shapeOf (lanetype_packtype pt)) (.mk_uN v.toNat))[index]! ≠ none
    rw [lanes_get _ _ _ valid]
    cases pt <;> simp [laneOfBits, lanetype_packtype, proj_lane__0]
  · simpa only [lanes_, proj_uN_0, unpackLanes_length] using valid
  · change _ = extend__ _ _ _ (Option.get! (proj_lane__0
      (lanes_ (shapeOf (lanetype_packtype pt)) (.mk_uN v.toNat))[index]!))
    rw [lanes_get _ _ _ valid]
    cases pt <;> rfl
  · cases pt <;> exact wf
  · exact const_wf v
  · have result := extract_wf (lanetype_packtype pt) index valid
    cases pt <;> exact result
  · apply wf_admininstr.admininstr_case_13
    cases pt <;> exact wf
  · exact shapeOf_wf _

theorem extract_step (ty : lanetype) (index : Nat) (v : BitVec 128)
    (valid : index < 128/lsize ty) :
    Step_pure [.VCONST .V128 (.mk_uN v.toNat),
      .VEXTRACT_LANE (shapeOf ty) (extractSign ty) (.mk_uN index)]
      [.CONST (unpack ty) (scalarOutput ty (v.toNat/2^(lsize ty*index)%2^lsize ty))] := by
  cases ty with
  | I32 => exact extract_num_step .I32 index v valid
  | I64 => exact extract_num_step .I64 index v valid
  | F32 => exact extract_num_step .F32 index v valid
  | F64 => exact extract_num_step .F64 index v valid
  | I8 => exact extract_pack_step .I8 index v valid
  | I16 => exact extract_pack_step .I16 index v valid

end Itasca.Runtime.Spec.Simd
