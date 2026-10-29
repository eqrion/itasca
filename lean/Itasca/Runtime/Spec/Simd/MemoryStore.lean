import Itasca.Runtime.Spec.MemoryStore
import Itasca.Runtime.Spec.Simd.Bitwise

/-!
Source reduction for bounded full-vector stores.

Main declarations: `full_store_step`. A direct consumer is `Interp.Simd.Memory.StoreSource`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt
theorem full_store_step (s : store) (f : frame) (argument : memarg) (address : Nat) (value : BitVec 128)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VSTORE .V128 argument))
    (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN value.toNat),.VSTORE .V128 argument]⟩ []
      (if address + proj_uN_0 argument.OFFSET + 16 ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨memoryPayloadWrite s f (address + proj_uN_0 argument.OFFSET) (vbytes_ .V128 (.mk_uN value.toNat)),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  have byteCount : rat_to_nat ((Option.get! (size valtype.V128) : Rat) / 8) = 16 := by
    norm_num [size,rat_to_nat]
    rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.VCONST .V128 (.mk_uN value.toNat),.VSTORE .V128 argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf value
    · exact operationWf)
  split
  · rename_i inside
    have updatedWf := memoryPayloadWrite_wf s f (address+proj_uN_0 argument.OFFSET) (vbytes_ .V128 (.mk_uN value.toNat))
      storeWf (by exact integerBytes_wf 16 value.toNat)
    apply StepH.step
    apply Step.vstore_val _ _ _ _ (vbytes_ .V128 (.mk_uN value.toNat))
    · simp [proj_num__0]
    · decide
    · exact .fun_with_mem_case_0 s f (.mk_uN 0) _ _ _ mapped
        (by simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using inside)
        (.state_case_0 _ _ updatedWf frameWf) (.state_case_0 _ _ storeWf frameWf)
    · rfl
    · exact input
    · exact wf_config_make updatedWf frameWf (forall_nil _)
  · rename_i outside
    apply StepH.step
    apply Step.vstore_oob
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact wf_config_trap storeWf frameWf
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd
