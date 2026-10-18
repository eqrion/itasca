import Exec.Spec.SimdMemoryLoad
import Exec.Spec.SimdReplace
namespace Exec.Spec.Simd
open SpecExt SpecExt.Builtins

theorem lane_byte_count (ty : Jnn) :
    rat_to_nat ((lsize (lanetype_Jnn ty) : Rat)/8) = lsize (lanetype_Jnn ty)/8 := by
  cases ty <;> norm_num [lsize,lanetype_Jnn,rat_to_nat,size,valtype_numtype,psize] <;> rfl

theorem lane_dimension (ty : Jnn) :
    ((128/lsize (lanetype_Jnn ty) : Nat) : Rat) = (128 : Rat)/lsize (lanetype_Jnn ty) := by
  cases ty <;> norm_num [lsize,lanetype_Jnn,size,valtype_numtype,psize]

theorem lane_load_value (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before result : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (bytesEq : ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN word.toNat) =
      ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take (lsize (lanetype_Jnn ty)/8))
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat)).set index (.mk_lane__0 ty (.mk_uN word.toNat)))) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN result.toNat)]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.VCONST .V128 (.mk_uN result.toNat)] from by
    simpa [Forall] using const_wf result)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.vload_lane_val _ _ _ _ _ _ _ (.mk_uN word.toNat) ty (128/lsize (lanetype_Jnn ty))
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using bytesEq
  · cases ty <;> rfl
  · exact lane_dimension ty
  · simpa only [shapeOf,List.modify_eq_set,proj_uN_0] using packed
  · exact input
  · exact const_wf result
  · exact Segment.index_wf 0 (by norm_num)
  · exact shapeOf_wf _
  · cases ty <;> exact laneOfBits_wf _ word.toNat word.isLt

theorem lane_load_trap (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before : BitVec 128) (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
  apply Step_read.vload_lane_oob
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using outside
  · exact input
  · exact .admininstr_case_73
  · exact Segment.index_wf 0 (by norm_num)
end Exec.Spec.Simd
