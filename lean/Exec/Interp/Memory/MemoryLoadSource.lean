import Exec.Interp.Memory.MemoryEncoding
import Exec.Spec.MemoryLoad

namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp
