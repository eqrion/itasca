import Itasca.Runtime.Spec.Simd.Bitwise
import Itasca.Runtime.Spec.Float
import SpecExt.Builtins.Float.Decoding

/-!
Source lane shapes and scalar input types.

Main declarations: `shapeOf` and `scalarInput`. A direct consumer is `Spec.PureWf`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def shapeOf (ty : lanetype) : shape := .X ty (.mk_dim (128/lsize ty))

theorem shape_of_wf (ty : lanetype) : wf_shape (shapeOf ty) := by
  cases ty <;> constructor
  all_goals first | exact .dim_case_0 _ (by decide) | decide

theorem shape_of_covers (ty : lanetype) : lsize ty * (128/lsize ty) = 128 := by
  cases ty <;> decide

theorem lane_of_bits_wf (ty : lanetype) (bits : Nat) (bound : bits < 2^lsize ty) :
    wf_lane_ ty (laneOfBits ty bits) := by
  cases ty with
  | I8 => exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 8 bits bound) rfl
  | I16 => exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 16 bits bound) rfl
  | I32 => exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 32 bits bound) rfl
  | I64 => exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 64 bits bound) rfl
  | F32 => exact .lane__case_1 _ _ _ (floatOfBits_wf_32 bits bound) rfl
  | F64 => exact .lane__case_1 _ _ _ (floatOfBits_wf_64 bits bound) rfl

def scalarInput (ty : lanetype) (bits : BitVec 64) : num_ :=
  match ty with
  | .I8 | .I16 | .I32 => .mk_num__0 .I32 (.mk_uN (bits.setWidth 32).toNat)
  | .I64 => .mk_num__0 .I64 (.mk_uN bits.toNat)
  | .F32 => .mk_num__1 .F32 (floatOfBits 32 (bits.setWidth 32).toNat)
  | .F64 => .mk_num__1 .F64 (floatOfBits 64 bits.toNat)

theorem scalar_input_wf (ty : lanetype) (bits : BitVec 64) :
    wf_num_ (unpack ty) (scalarInput ty bits) := by
  cases ty with
  | I8 | I16 | I32 => exact unsigned_num_wf .I32 _ (BitVec.toNat_lt_twoPow_of_le (by rfl))
  | I64 => exact unsigned_num_wf .I64 _ (BitVec.toNat_lt_twoPow_of_le (by rfl))
  | F32 => exact float_num_wf .F32 _ (floatOfBits_wf_32 _ (BitVec.toNat_lt_twoPow_of_le (by rfl)))
  | F64 => exact float_num_wf .F64 _ (floatOfBits_wf_64 _ (BitVec.toNat_lt_twoPow_of_le (by rfl)))

theorem pack_scalar_input (ty : lanetype) (bits : BitVec 64) :
    fun_packnum_ ty (scalarInput ty bits)
      (some (laneOfBits ty (bits.setWidth (lsize ty)).toNat)) := by
  have wf := lane_of_bits_wf ty (bits.setWidth (lsize ty)).toNat
    (BitVec.toNat_lt_twoPow_of_le (by rfl))
  cases ty with
  | I32 => exact .fun_packnum__case_0 _ wf
  | I64 =>
    change fun_packnum_ .I64 _ (some (.mk_lane__0 .I64 (.mk_uN (bits.setWidth 64).toNat)))
    rw [BitVec.setWidth_eq]
    exact .fun_packnum__case_1 _ wf
  | F32 => exact .fun_packnum__case_2 _ wf
  | F64 =>
    change fun_packnum_ .F64 _ (some (.mk_lane__1 .F64 (floatOfBits 64 (bits.setWidth 64).toNat)))
    rw [BitVec.setWidth_eq]
    exact .fun_packnum__case_3 _ wf
  | I8 =>
    have truncated : wrap__ 32 8 (.mk_uN (bits.setWidth 32).toNat) =
        .mk_uN (bits.setWidth 8).toNat := by
      simp only [wrap__, BitVec.toNat_setWidth, proj_uN_0]
      congr 1
      exact Nat.mod_mod_of_dvd _ (by decide : 2^8 ∣ 2^32)
    have wf' : wf_lane_ .I8 (.mk_lane__0 .I8 (wrap__ 32 8 (.mk_uN (bits.setWidth 32).toNat))) := by
      rw [truncated]; exact wf
    have result := fun_packnum_.fun_packnum__case_4 (.mk_uN (bits.setWidth 32).toNat) (by decide) wf'
    change fun_packnum_ .I8 _ (some (.mk_lane__0 .I8 (wrap__ 32 8 (.mk_uN (bits.setWidth 32).toNat)))) at result
    rw [truncated] at result
    exact result
  | I16 =>
    have truncated : wrap__ 32 16 (.mk_uN (bits.setWidth 32).toNat) =
        .mk_uN (bits.setWidth 16).toNat := by
      simp only [wrap__, BitVec.toNat_setWidth, proj_uN_0]
      congr 1
      exact Nat.mod_mod_of_dvd _ (by decide : 2^16 ∣ 2^32)
    have wf' : wf_lane_ .I16 (.mk_lane__0 .I16 (wrap__ 32 16 (.mk_uN (bits.setWidth 32).toNat))) := by
      rw [truncated]; exact wf
    have result := fun_packnum_.fun_packnum__case_5 (.mk_uN (bits.setWidth 32).toNat) (by decide) wf'
    change fun_packnum_ .I16 _ (some (.mk_lane__0 .I16 (wrap__ 32 16 (.mk_uN (bits.setWidth 32).toNat)))) at result
    rw [truncated] at result
    exact result

theorem splat_step (ty : lanetype) (bits : BitVec 64) (result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf ty)
      (List.replicate (128/lsize ty) (laneOfBits ty (bits.setWidth (lsize ty)).toNat))) :
    Step_pure [.CONST (unpack ty) (scalarInput ty bits), .VSPLAT (shapeOf ty)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  exact .vsplat ty (scalarInput ty bits) (128/lsize ty) (.mk_uN result.toNat)
    (some (laneOfBits ty (bits.setWidth (lsize ty)).toNat))
    (pack_scalar_input ty bits) (by simp) packed
    (.admininstr_case_13 _ _ (scalar_input_wf ty bits))
    (.admininstr_case_33 _ (shape_of_wf ty)) (const_wf result) (shape_of_wf ty)

end Itasca.Runtime.Spec.Simd
