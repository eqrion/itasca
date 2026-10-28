import Itasca.Runtime.Spec.SimdBitmaskBits
import Itasca.Runtime.Spec.SimdShiftSource
import Itasca.Runtime.Spec.IntegerSigned
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def bitmaskSource (ty : Jnn) : admininstr :=
  .VBITMASK (.mk_ishape (shapeOf (lanetype_Jnn ty)))

theorem bitmask_lane (width : Nat) (bits : BitVec width) :
    fun_ilt_ width .S (.mk_uN bits.toNat) (.mk_uN 0) (.mk_uN bits.msb.toNat) := by
  have relation := fun_ilt_.fun_ilt__case_1 width (.mk_uN bits.toNat) (.mk_uN 0)
    (0 : Int) bits.toInt (by simpa only [BitVec.toNat_zero,BitVec.toInt_zero,proj_uN_0] using bitvec_signed width (0#width)) (bitvec_signed width bits)
    (boolean_u32_wf (decide (bits.toInt < 0)))
  have boolean : decide (bits.toInt < 0) = bits.msb := by
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq,BitVec.msb_eq_true_iff_two_mul_ge,BitVec.toInt_neg_iff])
  cases h : bits.msb <;> simpa [nat_of_bool,boolean,h,Bool.toNat] using relation

theorem bitmask_step (ty : Jnn) (bits : BitVec 128) (result : BitVec 32)
    (mask : ∀ i, i<32 → result.getLsbD i =
      if i < 128/lsize (lanetype_Jnn ty) then (vectorLane (lanetype_Jnn ty) bits i).msb else false) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),bitmaskSource ty]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN result.toNat))] := by
  let count := 128/lsize (lanetype_Jnn ty)
  have countBound : count ≤ 32 := by cases ty <;> decide
  let inputs := (List.range count).map
    (fun j => lane_.mk_lane__0 ty (.mk_uN (vectorLane (lanetype_Jnn ty) bits j).toNat))
  let outputs := (List.range count).map
    (fun j => uN.mk_uN (vectorLane (lanetype_Jnn ty) bits j).msb.toNat)
  have inputEq : inputs = lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN bits.toNat) := by
    rw [vector_lanes]; cases ty <;> rfl
  have projected : Forall (fun lane => proj_lane__0 lane ≠ none) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp [proj_lane__0]
  have related : Forall₂ (fun out lane => fun_ilt_ (lsize (lanetype_Jnn ty)) .S
      (Option.get! (proj_lane__0 lane)) (.mk_uN 0) out) outputs inputs := by
    intro pair member
    rw [List.zip_map'] at member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact bitmask_lane _ _
  have listEq : ibits_ 32 (.mk_uN result.reverse.toNat) =
      outputs.map (fun out => bit.mk_bit (proj_uN_0 out)) ++
        List.replicate (Int.toNat ((32:Int)-count)) (.mk_bit 0) := by
    have countInt : Int.toNat ((32:Int)-count) = 32-count := by omega
    rw [countInt]
    apply List.ext_getElem
    · simp [ibits_,integerBits_length,outputs]; omega
    · intro i left right
      have valid : i<32 := by simpa only [ibits_,integerBits_length] using left
      simp only [ibits_,proj_uN_0]
      rw [integerBits_getMsb 32 result.reverse i valid,BitVec.getMsbD_reverse,mask i valid]
      change bit.mk_bit (if i<count then _ else false).toNat = _
      by_cases within : i<count
      · rw [List.getElem_append_left (by simp only [List.length_map,outputs,List.length_range]; exact within)]
        simp only [outputs,List.getElem_map,List.getElem_range,proj_uN_0,if_pos within]
      · rw [List.getElem_append_right (by simp only [List.length_map,outputs,List.length_range]; omega)]
        simp only [List.getElem_replicate,if_neg within,Bool.toNat_false]
  have outputWf : Forall (fun out => wf_bit (.mk_bit (proj_uN_0 out))) outputs := by
    intro out member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    cases (vectorLane (lanetype_Jnn ty) bits j).msb <;> constructor <;> simp [proj_uN_0]
  have reverseEq := irev_reverse 32 result
  rw [←reverseEq]
  apply Step_pure.vbitmask _ ty count _ inputs outputs
  · simp [inputs,outputs]
  · exact projected
  · exact related
  · exact inputEq
  · exact listEq
  · exact const_wf bits
  · apply wf_admininstr.admininstr_case_30
    exact .ishape_case_0 ty _ (shapeOf_wf _) rfl
  · rw [reverseEq]
    exact .admininstr_case_13 _ _ (unsigned_num_wf .I32 result.toNat result.isLt)
  · exact shapeOf_wf _
  · exact outputWf
  · constructor; simp
end Itasca.Runtime.Spec.Simd
