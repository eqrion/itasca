import Exec.Spec.MemoryFillSource
import Exec.Spec.FillSlice
namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem memoryFill_eq (s : store) (f : frame) (destination value count : Nat)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (inside : destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    memoryFill s f destination value count =
      {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun memory =>
        {memory with BYTES := fillInto memory.BYTES destination (fillByte value) count})} := by
  induction count generalizing s destination with
  | zero =>
    simp only [memoryFill,fillInto]
    have identity : (fun memory : meminst => {memory with BYTES := memory.BYTES}) = id := by funext memory; cases memory; rfl
    rw [identity,List.modify_id]
  | succ count ih =>
    by_cases done : count=0
    · subst count
      simp only [memoryFill,fillInto,memoryWrite]
    · have dstBound : destination+1 < 2^32 := by omega
      have dstNext : next32 destination = destination+1 := Nat.mod_eq_of_lt dstBound
      have lengthEq := memoryWrite_mem_length s f destination (fillByte value) address
      rw [memoryFill,dstNext,ih (memoryWrite s f destination (fillByte value)) (destination+1)
        (by simpa [memoryWrite] using address)
        (by simpa only [lengthEq] using memoryBound) (by rw [lengthEq]; omega)]
      simp only [memoryWrite,List.modify_modify_eq,Function.comp_def,fillInto]
end Itasca.Runtime.Spec.Segment
