import Itasca.Runtime.Interp.Relations.PackedMemory

namespace Itasca.Runtime.Interp.PackedMemory
open Aeneas Aeneas.Std SpecExt

private theorem machineBytes_wf (bytes : List U8) : Forall wf_byte (Store.decodeBytes bytes) := by
  intro byte member
  obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
  constructor
  scalar_tac

theorem load_word_decodes (op : Spec.PackedMemory) (sign : sx) (bytes : List U8) (start : Nat)
    (inside : start + op.bytes ≤ bytes.length) :
    Store.decodeWords (numericMemoryType (numtype_Inn op.type))
      (scalarLoadedWord (loadOpcode op sign) (scalarLoadBytes bytes start 0#u64 0 op.bytes)) 0#u64 =
      .CONST (numtype_Inn op.type) (op.loaded sign (Store.decodeBytes ((bytes.drop start).take op.bytes))) := by
  have width : op.bytes ≤ 8 := by cases op <;> decide
  have wordEq := scalarLoadBytes_source bytes start op.bytes width inside
  have payloadWf := machineBytes_wf ((bytes.drop start).take op.bytes)
  have payloadLength : (Store.decodeBytes ((bytes.drop start).take op.bytes)).length = op.bytes := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  have bounded := Spec.integerOfBytes_bound _ payloadWf
  rw [payloadLength] at bounded
  have power : 256^op.bytes = 2^op.bits := by cases op <;> decide
  rw [power] at bounded
  rw [load_word_value op sign _ (by rw [wordEq]; exact bounded)]
  simp only [Spec.PackedMemory.loaded,inv_ibytes_,wordEq]

end Itasca.Runtime.Interp.PackedMemory
