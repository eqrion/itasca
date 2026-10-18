import Exec.Interp.Memory.MemoryCoreStore
namespace Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std
 theorem dispatch_load_core_values {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M)
    (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index raw.instance raw.function raw.base
      (Code.memoryLoadInstruction op address address offset) ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (      (∃ nextFrame, out.1 = .Ok () ∧ Abs.Core.load s f rest after op argument = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec) ∨
      ((out.1,out.2.1) = (.Err (.Trap .MemoryOutOfBounds),exec) ∧ Abs.Core.load s f rest after op argument = .trap)) ⦄ := by
  apply WP.spec_mono (dispatch_load memory hooks floats allocator exec store platform index raw.instance raw.function raw.base op address address offset
    (execute_load_core memory view laws code exec store raw op address offset inst memoryAddress object s f rest after front bits argument found mapped issued storeEq moduleEq values slots addressSlot bitsBound offsetEq))
  intro out effect
  exact ⟨effect.2.1,effect.2.2,effect.1⟩
 theorem dispatch_store_core_values {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M)
    (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (number : num_) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index raw.instance raw.function raw.base
      (Code.memoryStoreInstruction op address value offset) ⦃ out =>
      out.2.1 = exec ∧ out.2.2.2 = platform ∧
      (      MemoryMutation view store out.2.2.1 memoryAddress object ∧
      ((out.1 = .Ok () ∧ Abs.Core.store s f rest after op argument =
          .next {s with store := Store.decodeStore view code out.2.2.1, frames := {f with code := after, vals := front} :: rest} ∧
        FrameSlots exec raw {f with code := after, vals := front}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Abs.Core.store s f rest after op argument = .trap ∧
        Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store))) ⦄ := by
  apply WP.spec_mono (dispatch_store memory hooks floats allocator exec store platform index raw.instance raw.function raw.base op address value offset
    (execute_store_core_values memory view laws code exec store raw op address value offset inst memoryAddress object s f rest after front bits number argument found mapped issued storeEq moduleEq values slots addressSlot valueSlot bitsBound numberWf offsetEq))
  intro out effect
  exact ⟨effect.2.1,effect.2.2,effect.1⟩
end Exec.Interp.MemoryDescriptor
