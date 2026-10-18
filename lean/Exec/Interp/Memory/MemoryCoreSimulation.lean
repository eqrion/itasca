import Exec.Interp.Memory.MemoryCoreDispatch
import Exec.Abs.Core.MemoryLoad
import Exec.Abs.Core.MemoryStore
namespace Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Exec.Spec
 theorem execute_load_core_simulation {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.execute_load memory exec store raw.instance raw.base (loadOpcode op) address address offset ⦃ out =>
      (∃ nextFrame, out.1 = .Ok () ∧
        Abs.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2 raw nextFrame ∧ {out.2 with slots := exec.slots} = exec) ∨
      (out = (.Err (.Trap .MemoryOutOfBounds),exec) ∧ ∃ n, 0 < n ∧
        StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩) ⦄ := by
  dsimp only
  have source := Abs.Core.load_progress (Store.decodeStore view code store) ambient f rest after op argument typed
  apply WP.spec_mono (execute_load_core memory view laws code exec store raw op address offset inst memoryAddress object
    ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after front bits argument found mapped issued rfl moduleEq values slots addressSlot bitsBound offsetEq)
  intro out effect
  rcases effect with ⟨nextFrame,success,actual,slotsAfter,unchanged⟩ | ⟨failed,actual⟩
  · rcases source with ⟨next,abstract,fresh,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      cases abstract
      exact Or.inl ⟨nextFrame,success,fresh,step,slotsAfter,unchanged⟩
    · rw [actual] at trapped
      contradiction
  · rcases source with ⟨next,abstract,fresh,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      contradiction
    · exact Or.inr ⟨failed,trace⟩
 theorem execute_store_core_simulation {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.Instance)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.Memory M)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (number : num_) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.execute_store memory exec store raw.instance raw.base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      ((out.1 = .Ok () ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2, frames := {f with code := after,vals := front} :: rest} ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2) ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with store := Store.decodeStore view code out.2, frames := {f with code := after,vals := front} :: rest}) ∧
        FrameSlots exec raw {f with code := after,vals := front}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have source := Abs.Core.store_progress (Store.decodeStore view code store) ambient f rest after op argument typed
  apply WP.spec_mono (execute_store_core_values memory view laws code exec store raw op address value offset inst memoryAddress object
    ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after front bits number argument found mapped issued rfl moduleEq values slots addressSlot valueSlot bitsBound numberWf offsetEq)
  intro out effect
  refine ⟨effect.1,?_⟩
  rcases effect.2 with ⟨success,actual,slotsAfter⟩ | ⟨failed,actual,unchanged⟩
  · rcases source with ⟨next,abstract,fresh,extension,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      cases abstract
      exact Or.inl ⟨success,fresh,extension,step,slotsAfter⟩
    · rw [actual] at trapped
      contradiction
  · rcases source with ⟨next,abstract,fresh,extension,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      contradiction
    · exact Or.inr ⟨failed,unchanged,trace⟩
end Exec.Interp.MemoryDescriptor
