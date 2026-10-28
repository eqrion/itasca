import Itasca.Runtime.Spec.MemoryInitSource
import Itasca.Runtime.Spec.SegmentCopy

namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem memoryInit_eq (s : store) (f : frame) (dataIndex destination source count : Nat)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (dataBound : (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ≤ 2^32)
    (inside : source+count ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧
      destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    memoryInit s f dataIndex destination source count =
      {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun memory =>
        {memory with BYTES := copyInto memory.BYTES (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES destination source count})} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [memoryInit,copyInto]
    have identity : (fun memory : meminst => {memory with BYTES := memory.BYTES}) = id := by funext memory; cases memory; rfl
    rw [identity,List.modify_id]
  | succ count ih =>
    by_cases done : count = 0
    · subst count
      simp only [memoryInit,copyInto,memoryWrite,fun_data,proj_uN_0]
    · have dstBound : destination+1 < 2^32 := by omega
      have srcBound : source+1 < 2^32 := by omega
      have dstNext : next32 destination = destination+1 := Nat.mod_eq_of_lt dstBound
      have srcNext : next32 source = source+1 := Nat.mod_eq_of_lt srcBound
      have lengthEq := memoryWrite_mem_length s f destination
        ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!) address
      rw [memoryInit,dstNext,srcNext,ih (memoryWrite s f destination ((fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES[source]!)) (destination+1) (source+1)
        (by simpa [memoryWrite] using address)
        (by simpa only [lengthEq] using memoryBound) dataBound
        (by rw [lengthEq]; change source+1+count ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧ _; omega)]
      simp only [memoryWrite,fun_data,proj_uN_0,List.modify_modify_eq,Function.comp_def,copyInto]

end Itasca.Runtime.Spec.Segment
