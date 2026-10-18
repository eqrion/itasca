import Exec.Interp.Memory.MemoryCore
import Exec.Interp.Control.StructuredPoint
namespace Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem core_load_next_shape {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (memoryAddress : runtime.MemoryAddr)
    (object : runtime.store.Memory M) (s : Abs.AState) (f nextFrame : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (bits : Nat) (op : Abs.Memory.Load) (argument : memarg) (offset : U32)
    (storeEq : s.store = Store.decodeStore view code store) (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits]) (bound : bits < 2^32)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (actual : Abs.Core.load s f rest after op argument = .next {s with frames := nextFrame :: rest}) :
    ∃ value, nextFrame = {f with code := after,vals := front ++ [value]} ∧
      Code.valueType value = valtype_numtype op.type := by
  rw [core_load_value view code store inst memoryAddress object s f rest after front bits op argument offset
    storeEq moduleEq mapped issued values bound offsetEq] at actual
  split at actual
  · have same := congrArg Abs.AState.frames (Abs.AResult.next.inj actual)
    have frameEq := (List.cons.inj same).1
    exact ⟨_,frameEq.symm,by rw [valueType_eq_abs]; exact op.value_type _⟩
  · contradiction
end Exec.Interp.MemoryDescriptor
