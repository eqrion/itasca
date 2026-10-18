import Exec.Spec.SimdMemoryLoad
namespace Exec.Spec.Simd
open SpecExt SpecExt.Builtins

def zeroLoadResult (width : Nat) (bytes : List byte) (start : Nat) : List admininstr :=
  if start + width/8 ≤ bytes.length then
    [.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))]
  else [.TRAP]

theorem zero_load_step (width : Nat) (supported : width = 32 ∨ width = 64)
    (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument]⟩ []
      ⟨⟨s,f⟩,zeroLoadResult width (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
        (address + proj_uN_0 argument.OFFSET)⟩ := by
  have byteCount : rat_to_nat ((width : Rat) / 8) = width/8 := by
    rcases supported with rfl | rfl <;> norm_num [rat_to_nat] <;> rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  unfold zeroLoadResult
  split
  · rename_i fits
    let bytes := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
    let start := address + proj_uN_0 argument.OFFSET
    have payloadWf : Forall wf_byte ((bytes.drop start).take (width/8)) := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : ((bytes.drop start).take (width/8)).length = width/8 := by
      simp only [List.length_take,List.length_drop]
      dsimp only [bytes,start]
      omega
    have bounded := integerOfBytes_bound _ payloadWf
    rw [payloadLength] at bounded
    have narrow : wf_uN width (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8)))) := by
      apply unsigned_wf_of_lt
      rcases supported with rfl | rfl <;> norm_num at bounded ⊢ <;> exact bounded
    have valueWf : wf_admininstr (.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))) := by
      apply wf_admininstr.admininstr_case_20 _ _ (by decide)
      apply unsigned_wf_of_lt
      rcases supported with rfl | rfl <;> norm_num [size,valtype_vectype] at bounded ⊢ <;> omega
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))] from by
      simpa [Forall] using valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    apply Step_read.vload_zero_val _ _ _ _ _ (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))
    · simp [proj_num__0]
    · have roundtrip := integerBytes_ofBytes _ payloadWf
      rw [payloadLength] at roundtrip
      simpa only [ibytes_,proj_uN_0,byteCount,proj_num__0,Option.get!_some,bytes,start,payloadLength]
        using roundtrip
    · rfl
    · exact narrow
    · exact input
    · exact valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.vload_zero_oob
    · simp [proj_num__0]
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)
end Exec.Spec.Simd
