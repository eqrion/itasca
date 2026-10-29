import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryOpcode
import Itasca.Runtime.Interp.Memory.MemoryValueSlots
import Itasca.Runtime.SourceMachine.Core.MemoryStep

/-!
Scalar load dispatch and core execution. Bytecode dispatch equations and destination-slot effects assemble the core scalar load correspondence.
-/

/-! ## Memory Dispatch Bridge -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_load_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : Abs.Memory.Load) (dst address offset : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.memoryLoadInstruction op dst address offset) = (do
        let (result,next) ← runtime.interp.execute_load memory exec store inst base (loadOpcode op) dst address offset
        Result.ok (result,next,store,platform)) := by
  cases op with
  | full ty => cases ty <;> simp [Code.memoryLoadInstruction,runtime.interp.dispatch,
      runtime.interp.dispatch_load,runtime.interp.load_operands,loadOpcode,numericLoadOpcode,bind_ok]
  | packed ty width sign => cases ty <;> cases width <;> cases sign <;>
    simp [Code.memoryLoadInstruction,runtime.interp.dispatch,runtime.interp.dispatch_load,
      runtime.interp.load_operands,loadOpcode,packed,PackedMemory.loadOpcode,bind_ok]

theorem dispatch_store_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : Abs.Memory.Store) (address value offset : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.memoryStoreInstruction op address value offset) = (do
        let (result,next) ← runtime.interp.execute_store memory exec store inst base (storeOpcode op) address value offset
        Result.ok (result,exec,next,platform)) := by
  cases op with
  | full ty => cases ty <;> simp [Code.memoryStoreInstruction,runtime.interp.dispatch,
      runtime.interp.dispatch_store,runtime.interp.store_operands,storeOpcode,numericStoreOpcode,bind_ok]
  | packed ty width => cases ty <;> cases width <;>
    simp [Code.memoryStoreInstruction,runtime.interp.dispatch,runtime.interp.dispatch_store,
      runtime.interp.store_operands,storeOpcode,packed,PackedMemory.storeOpcode,bind_ok]

theorem dispatch_load {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (op : Abs.Memory.Load) (dst address offset : U32)
    (handler : runtime.interp.execute_load memory exec store inst base (loadOpcode op) dst address offset ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.memoryLoadInstruction op dst address offset) ⦃ out =>
        Q (out.1,out.2.1) ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  rw [dispatch_load_eq]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl,rfl⟩

theorem dispatch_store {Q : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (op : Abs.Memory.Store) (address value offset : U32)
    (handler : runtime.interp.execute_store memory exec store inst base (storeOpcode op) address value offset ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.memoryStoreInstruction op address value offset) ⦃ out =>
        Q (out.1,out.2.2.1) ∧ out.2.1 = exec ∧ out.2.2.2 = platform ⦄ := by
  rw [dispatch_store_eq]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl,rfl⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Load Slots -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem execute_load_slots {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (front : List val) (bits : Nat)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : ValuesAt exec.slots.val base.val (front ++ [Abs.integerVal .I32 bits]))
    (addressSlot : address.val = Code.slots (front.map Code.valueType))
    (bitsBound : bits < 2^32) :
    runtime.interp.execute_load memory exec store instanceIndex base (loadOpcode op) address address offset ⦃ out =>
      if bits + offset.val + op.bytes ≤ (view object.buf).length then
        out.1 = .Ok () ∧
        ValuesAt out.2.slots.val base.val (front ++ [op.value
          (Store.decodeBytes (((view object.buf).val.drop (bits+offset.val)).take op.bytes))]) ∧
        {out.2 with slots := exec.slots} = exec
      else out = (.Err (.Trap .MemoryOutOfBounds),exec) ⦄ := by
  have words : WordsAt exec.slots.val base.val (Code.encodeValues front ++ [bits]) := by
    simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,Code.encodeValue,Abs.integerVal,
      numtype_Inn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using values
  have tail := words.append_right
  obtain ⟨bound,wordEq⟩ := tail 0 (by simp)
  have addressPosition : address.val = (Code.encodeValues front).length := by simpa only [Code.encodeValues_length] using addressSlot
  have atBound : base.val + address.val < exec.slots.length := by simpa only [Nat.add_zero,←addressPosition] using bound
  let word := exec.slots.val[base.val+address.val]
  have input : exec.slots.val[base.val+address.val]? = some word := List.getElem?_eq_getElem atBound
  have actual : word.val = bits := by
    have concrete : exec.slots.val[base.val+address.val]!.val = bits := by
      simpa only [Nat.add_zero,←addressPosition,List.getElem!_cons_zero] using wordEq
    simpa only [_root_.getElem!_pos exec.slots.val (base.val+address.val) atBound] using concrete
  have castEq : (UScalar.cast .U32 word).val = bits := by scalar_tac
  apply WP.spec_mono (execute_load_effect memory view laws exec store instanceIndex base (loadOpcode op) address address offset
    inst memoryAddress object word found mapped issued input atBound)
  intro out effect
  rw [load_width,castEq] at effect
  split at effect
  · rename_i inside
    rw [if_pos inside]
    refine ⟨effect.1,?_,effect.2.2⟩
    rw [effect.2.1]
    have updated := words.append_left.set_append
      (scalarLoadedWord (loadOpcode op) (scalarLoadBytes (view object.buf).val (bits+offset.val) 0#u64 0 op.bytes))
      (by simpa only [←addressPosition] using atBound)
    rw [addressPosition]
    simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,load_word_encode op _ _ inside] using updated
  · rename_i outside
    rw [if_neg outside]
    exact effect
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Core -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem core_load_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (memoryAddress : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (bits : Nat) (op : Abs.Memory.Load) (argument : memarg) (offset : U32)
    (storeEq : s.store = Store.decodeStore view code store) (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits]) (bound : bits < 2^32)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    Abs.Core.load s f rest after op argument =
      if bits+offset.val+op.bytes ≤ (view object.buf).length then
        .next {s with frames := {f with code := after, vals := front ++ [op.value
          (Store.decodeBytes (((view object.buf).val.drop (bits+offset.val)).take op.bytes))]} :: rest}
      else .trap := by
  simp only [Abs.Core.load,values,Abs.pop_append,Abs.integerVal,Abs.integer,numtype_Inn,
    and_self,ite_true,true_and,if_pos bound,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,offsetEq,Store.decodeMemory,Store.decodeBytes,List.length_map,
    List.map_drop,List.map_take,Abs.advance]

 theorem execute_load_core {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
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
    runtime.interp.execute_load memory exec store raw.instance raw.base (loadOpcode op) address address offset ⦃ out =>
      (∃ nextFrame, out.1 = .Ok () ∧ Abs.Core.load s f rest after op argument = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2 raw nextFrame ∧ {out.2 with slots := exec.slots} = exec) ∨
      (out = (.Err (.Trap .MemoryOutOfBounds),exec) ∧ Abs.Core.load s f rest after op argument = .trap) ⦄ := by
  have actualValues : ValuesAt exec.slots.val raw.base.val ((f.locals++front) ++ [Abs.integerVal .I32 bits]) := by
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have actualAddress : address.val = Code.slots ((f.locals++front).map Code.valueType) := by
    simpa only [List.map_append,Code.slots_append] using addressSlot
  have abstract := core_load_value view code store inst memoryAddress object s f rest after front bits op argument offset
    storeEq moduleEq mapped issued values bitsBound offsetEq
  apply WP.spec_mono (execute_load_slots memory view laws exec store raw.instance raw.base op address offset inst memoryAddress object
    (f.locals++front) bits found mapped issued actualValues actualAddress bitsBound)
  intro out effect
  split at effect
  · rename_i inside
    rw [if_pos inside] at abstract
    exact Or.inl ⟨_,effect.1,abstract,by simpa only [FrameSlots,List.append_assoc] using effect.2.1,effect.2.2⟩
  · rename_i outside
    rw [if_neg outside] at abstract
    exact Or.inr ⟨effect,abstract⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end
