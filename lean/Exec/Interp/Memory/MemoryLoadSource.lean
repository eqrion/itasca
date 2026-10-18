import Exec.Interp.Memory.MemoryEncoding
import Exec.Spec.MemoryLoad

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

def numericLoadOpcode : numtype → U16
  | .I32 => 40#u16
  | .I64 => 41#u16
  | .F32 => 42#u16
  | .F64 => 43#u16

def numericMemoryType : numtype → Itasca.types.ValueType
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64

private theorem numericLoadOpcode_width (ty : numtype) :
    (scalarLoadWidth (numericLoadOpcode ty)).val = Spec.scalarNumBytes ty := by
  cases ty <;> rfl

private theorem numericLoadOpcode_word (ty : numtype) (word : U64) :
    scalarLoadedWord (numericLoadOpcode ty) word = word := by cases ty <;> rfl

private theorem machineBytes_wf (bytes : List U8) : Forall wf_byte (Store.decodeBytes bytes) := by
  intro byte member
  obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
  constructor
  scalar_tac

theorem numeric_load_word_decodes (ty : numtype) (bytes : List U8) (start : Nat)
    (inside : start + Spec.scalarNumBytes ty ≤ bytes.length) :
    Store.decodeWords (numericMemoryType ty)
      (scalarLoadBytes bytes start 0#u64 0 (Spec.scalarNumBytes ty)) 0#u64 =
      .CONST ty (inv_nbytes_ ty (Store.decodeBytes ((bytes.drop start).take (Spec.scalarNumBytes ty)))) := by
  have width : Spec.scalarNumBytes ty ≤ 8 := by cases ty <;> decide
  have wordEq := scalarLoadBytes_source bytes start (Spec.scalarNumBytes ty) width inside
  have payloadWf := machineBytes_wf ((bytes.drop start).take (Spec.scalarNumBytes ty))
  have payloadLength : (Store.decodeBytes ((bytes.drop start).take (Spec.scalarNumBytes ty))).length = Spec.scalarNumBytes ty := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  have bounded := Spec.integerOfBytes_bound _ payloadWf
  rw [payloadLength] at bounded
  cases ty <;> simp only [numericMemoryType,Store.decodeWords,wordEq,inv_nbytes_,inv_ibytes_,inv_fbytes_]
  · rw [Nat.mod_eq_of_lt (by simpa [Spec.scalarNumBytes] using bounded)]
  · rw [Nat.mod_eq_of_lt (by simpa [Spec.scalarNumBytes] using bounded)]

/-- All four full-width numeric load handlers refine the generated source rule.
The byte dictionary observation and source memory lookup are the only connection
between the machine buffer and the source store. -/
theorem memory_numeric_load_source (ty : numtype) (address offset : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.LOAD ty none argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val) :
    runtime.interp.memory.load (numericLoadOpcode ty) address offset bytes ⦃ result =>
      match result with
      | .Ok word => StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address.val,.LOAD ty none argument]⟩ []
          ⟨⟨s,f⟩,[admininstr_val (Store.decodeWords (numericMemoryType ty) word 0#u64)]⟩
      | .Err error => error = .Trap .MemoryOutOfBounds ∧
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address.val,.LOAD ty none argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have source := Spec.numeric_load_step s f ty argument address.val storeWf frameWf (by scalar_tac)
    operationWf (by rw [memoryEq]; exact machineBytes_wf bytes.val)
  simp only [Spec.numericLoadResult,memoryEq,offsetEq,Store.decodeBytes,List.length_map] at source
  apply WP.spec_mono (memory_load_effect (numericLoadOpcode ty) address offset bytes)
  intro result effect
  unfold ScalarLoadEffect at effect
  rw [numericLoadOpcode_width] at effect
  by_cases fits : address.val + offset.val + Spec.scalarNumBytes ty ≤ bytes.val.length
  · rw [if_pos fits] at source effect
    rw [effect,numericLoadOpcode_word]
    simpa only [numeric_load_word_decodes ty bytes.val (address.val+offset.val) fits,
      admininstr_val,Store.decodeBytes,List.map_take,List.map_drop] using source
  · rw [if_neg fits] at source effect
    rw [effect]
    exact ⟨rfl,source⟩
end Exec.Interp
