import Itasca.Runtime.Spec.MemoryLoad
import Itasca.Runtime.Spec.Simd.Bitwise

/-!
The source result relation for full-vector loads.

Main declarations: `fullLoadResult`. A direct consumer is `Spec.Simd.MemoryLane`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins

def fullLoadResult (bytes : List byte) (start : Nat) : List admininstr :=
  if start + 16 ≤ bytes.length then [.VCONST .V128 (inv_vbytes_ .V128 ((bytes.drop start).take 16))]
  else [.TRAP]

theorem vector_bytes_roundtrip (bytes : List byte) (valid : Forall wf_byte bytes)
    (sized : bytes.length = 16) : vbytes_ .V128 (inv_vbytes_ .V128 bytes) = bytes := by
  have roundtrip := integer_bytes_of_bytes bytes valid
  simpa [vbytes_,inv_vbytes_,ibytes_,inv_ibytes_,vsize,proj_uN_0,sized] using roundtrip

theorem vector_bytes_wf (bytes : List byte) (valid : Forall wf_byte bytes)
    (sized : bytes.length = 16) : wf_admininstr (.VCONST .V128 (inv_vbytes_ .V128 bytes)) := by
  have bounded := integer_of_bytes_bound bytes valid
  apply wf_admininstr.admininstr_case_20 _ _ (by decide)
  apply unsigned_wf_of_lt
  rw [sized] at bounded
  simpa [inv_vbytes_,inv_ibytes_,vsize,size,valtype_vectype] using bounded

theorem full_load_step (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 none argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VLOAD .V128 none argument]⟩ []
      ⟨⟨s,f⟩,fullLoadResult (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
        (address + proj_uN_0 argument.OFFSET)⟩ := by
  have byteCount : rat_to_nat ((Option.get! (size valtype.V128) : Rat) / 8) = 16 := by
    norm_num [size,rat_to_nat]
    rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.VLOAD .V128 none argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  unfold fullLoadResult
  split
  · rename_i fits
    let bytes := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
    let start := address + proj_uN_0 argument.OFFSET
    have payloadWf : Forall wf_byte ((bytes.drop start).take 16) := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : ((bytes.drop start).take 16).length = 16 := by
      simp only [List.length_take,List.length_drop]
      dsimp only [bytes,start]
      omega
    have valueWf := vector_bytes_wf _ payloadWf payloadLength
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [.VCONST .V128 (inv_vbytes_ .V128 ((bytes.drop start).take 16))] from by
      simpa [Forall] using valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    apply Step_read.vload_val
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some,bytes,start] using
        vector_bytes_roundtrip _ payloadWf payloadLength
    · exact input
    · exact valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.vload_oob
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd
