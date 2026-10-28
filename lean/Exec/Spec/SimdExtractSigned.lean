import Exec.Spec.SimdExtract
import Exec.Spec.IntegerExtend
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem signed_lane_num_wf (width bits : Nat) (bound : bits < 2^width) :
    wf_num_ .I32 (.mk_num__0 .I32 (extend__ width 32 .S (.mk_uN bits))) := by
  have eq := extend_signed_bitvec width 32 (BitVec.ofNat width bits)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at eq
  rw [eq]
  exact unsigned_num_wf .I32 _ (BitVec.toNat_lt_twoPow_of_le (by rfl))

theorem extract_signed_wf (ty : packtype) (index : Nat) (valid : index < 128/psize ty) :
    wf_admininstr (.VEXTRACT_LANE (shapeOf (lanetype_packtype ty)) (some .S) (.mk_uN index)) := by
  apply wf_admininstr.admininstr_case_34 _ _ _ (shapeOf_wf _) (index_wf (lanetype_packtype ty) index (by cases ty <;> exact valid)) (by decide)
  cases ty <;> decide

theorem extract_signed_step (ty : packtype) (index : Nat) (v : BitVec 128)
    (valid : index < 128/psize ty) :
    Step_pure [.VCONST .V128 (.mk_uN v.toNat),
      .VEXTRACT_LANE (shapeOf (lanetype_packtype ty)) (some .S) (.mk_uN index)]
      [.CONST .I32 (.mk_num__0 .I32
        (extend__ (psize ty) 32 .S (.mk_uN (v.toNat/2^(psize ty*index)%2^psize ty))))] := by
  have sizes : lsize (lanetype_packtype ty) = psize ty := by cases ty <;> rfl
  have wf := signed_lane_num_wf (psize ty) (v.toNat/2^(psize ty*index)%2^psize ty)
    (Nat.mod_lt _ (by positivity))
  apply Step_pure.vextract_lane_pack _ ty (128/lsize (lanetype_packtype ty)) .S (.mk_uN index)
  · simp [proj_num__0]
  · change proj_lane__0 (lanes_ (shapeOf (lanetype_packtype ty)) (.mk_uN v.toNat))[index]! ≠ none
    rw [lanes_get _ _ _ (by simpa only [sizes] using valid)]
    cases ty <;> simp [laneOfBits, lanetype_packtype, proj_lane__0]
  · simpa only [lanes_, proj_uN_0, unpackLanes_length, sizes] using valid
  · change _ = extend__ _ _ _ (Option.get! (proj_lane__0
      (lanes_ (shapeOf (lanetype_packtype ty)) (.mk_uN v.toNat))[index]!))
    rw [lanes_get _ _ _ (by simpa only [sizes] using valid)]
    cases ty <;> rfl
  · exact wf
  · exact const_wf v
  · exact extract_signed_wf ty index valid
  · exact .admininstr_case_13 _ _ wf
  · exact shapeOf_wf _

end Itasca.Runtime.Spec.Simd
