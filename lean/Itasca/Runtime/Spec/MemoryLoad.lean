import Itasca.Runtime.Spec.ByteEncoding
import Itasca.Runtime.Spec.SegmentInitCases

namespace Itasca.Runtime.Spec
open SpecExt

def numericLoadResult (ty : numtype) (bytes : List byte) (start : Nat) : List admininstr :=
  if start + scalarNumBytes ty ≤ bytes.length then
    [.CONST ty (inv_nbytes_ ty ((bytes.drop start).take (scalarNumBytes ty)))]
  else [.TRAP]

private theorem numeric_size_present (ty : numtype) : size (valtype_numtype ty) ≠ none := by
  cases ty <;> decide

private theorem numeric_byte_count (ty : numtype) :
    rat_to_nat ((Option.get! (size (valtype_numtype ty)) : Rat) / 8) = scalarNumBytes ty := by
  cases ty <;> norm_num [size,valtype_numtype,rat_to_nat,scalarNumBytes] <;> rfl

/-- A source numeric load returns the canonical little-endian decoding or takes
the generated bounds-trap rule. Both outcomes preserve the source store. -/
theorem numeric_load_step (s : store) (f : frame) (ty : numtype) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.LOAD ty none argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.LOAD ty none argument]⟩ []
      ⟨⟨s,f⟩,numericLoadResult ty (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
        (address + proj_uN_0 argument.OFFSET)⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.LOAD ty none argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  unfold numericLoadResult
  split
  · rename_i fits
    let bytes := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
    let start := address + proj_uN_0 argument.OFFSET
    have payloadWf : Forall wf_byte ((bytes.drop start).take (scalarNumBytes ty)) := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : ((bytes.drop start).take (scalarNumBytes ty)).length = scalarNumBytes ty := by
      simp only [List.length_take,List.length_drop]
      dsimp only [bytes,start]
      omega
    have valueWf := numericBytes_wf ty _ payloadWf payloadLength
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.CONST ty (inv_nbytes_ ty ((bytes.drop start).take (scalarNumBytes ty)))] from by
      simpa [Forall] using wf_admininstr.admininstr_case_13 _ _ valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    apply Step_read.load_num_val
    · simp [proj_num__0]
    · exact numeric_size_present ty
    · simpa only [numeric_byte_count,proj_num__0,proj_uN_0,Option.get!_some,bytes,start] using
        numericBytes_roundtrip ty _ payloadWf payloadLength
    · exact input
    · exact .admininstr_case_13 _ _ valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.load_num_trap
    · simp [proj_num__0]
    · exact numeric_size_present ty
    · simpa only [numeric_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec
