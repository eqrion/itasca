import Exec.Spec.SimdMemoryLane
namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins
theorem splat_load_value (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address : Nat)
    (result : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument))
    (bytesEq : ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN word.toNat) =
      ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take (lsize (lanetype_Jnn ty)/8))
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      (List.replicate (128/lsize (lanetype_Jnn ty)) (.mk_lane__0 ty (.mk_uN word.toNat)))) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,
      .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument]⟩ []
      ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN result.toNat)]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,
        .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.VCONST .V128 (.mk_uN result.toNat)] from by
    simpa [Forall] using const_wf result)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.vload_splat_val _ _ _ _ _ (.mk_uN word.toNat) ty (128/lsize (lanetype_Jnn ty))
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

theorem splat_load_trap (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument))
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,
      .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,
        .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
  apply Step_read.vload_splat_oob
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using outside
  · exact input
  · exact .admininstr_case_73
  · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd
