import Itasca.Runtime.Spec.SimdMemoryLane
import Itasca.Runtime.Spec.MemoryStore
namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins

theorem lane_store_step (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (valid : index < 128/lsize (lanetype_Jnn ty))
    (selected : (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]! = .mk_lane__0 ty (.mk_uN word.toNat))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ []
      (if address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8 ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨memoryPayloadWrite s f (address+proj_uN_0 argument.OFFSET)
          (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  split
  · rename_i inside
    have updatedWf := memoryPayloadWrite_wf s f (address+proj_uN_0 argument.OFFSET)
      (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat) storeWf (integerBytes_wf _ _)
    apply StepH.step
    apply Step.vstore_lane_val _ _ _ _ _ _ _ ty (128/lsize (lanetype_Jnn ty))
    · simp [proj_num__0]
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some,memoryPayloadWrite] using
        fun_with_mem.fun_with_mem_case_0 s f (.mk_uN 0) (address+proj_uN_0 argument.OFFSET)
          (lsize (lanetype_Jnn ty)/8) (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat) mapped inside
          (.state_case_0 _ _ updatedWf frameWf) (.state_case_0 _ _ storeWf frameWf)
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using inside
    · cases ty <;> rfl
    · exact lane_dimension ty
    · change proj_lane__0 ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!) ≠ none
      rw [selected]; simp [proj_lane__0]
    · simpa [lanes_,shapeOf,proj_uN_0,unpackLanes_length] using valid
    · change integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat =
        ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0
          ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!)))))
      rw [selected]
      rfl
    · exact input
    · exact wf_config_make updatedWf frameWf (forall_nil _)
    · exact Segment.index_wf 0 (by norm_num)
    · change wf_uN (lsize (lanetype_Jnn ty)) (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0
        ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!)))))
      rw [selected]
      exact unsigned_wf_of_lt _ word.toNat word.isLt
  · rename_i outside
    apply StepH.step
    apply Step.vstore_lane_oob
    · simp [proj_num__0]
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using
        (Nat.lt_of_not_ge outside)
    · exact input
    · exact wf_config_trap storeWf frameWf
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd
