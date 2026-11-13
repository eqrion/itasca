import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.State.TableAccess

/-!
Sections, each formerly its own module: MemoryLoadStepFootprint, MemoryGrow.
-/

/-! ## MemoryLoadStepFootprint -/

section

/-!
Scalar load slot footprint through dispatch and fetch. The step proof lifts the concrete destination write while retaining every other execution field.
-/

/-! ## Memory Load Footprint -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem execute_load_footprint {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : SourceMachine.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (front : List val) (bits : Nat)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : ValuesAt exec.slots.val base.val (front ++ [SourceMachine.integerVal .I32 bits]))
    (addressSlot : address.val = Compiler.slots (front.map Compiler.valueType))
    (bitsBound : bits < 2^32) :
    runtime.interp.execute_load memory exec store instanceIndex base (loadOpcode op) address address offset ⦃ out =>
      out.1 = .Ok () → ∃ word, base.val+address.val < exec.slots.length ∧
        SlotsEffect exec out.2 (exec.slots.val.set (base.val+address.val) word) ⦄ := by
  have words : WordsAt exec.slots.val base.val (Compiler.encodeValues front ++ [bits]) := by
    simpa only [ValuesAt,Compiler.encode_values_append,Compiler.encodeValues,Compiler.encodeValue,SourceMachine.integerVal,
      numtype_Inn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using values
  have tail := words.append_right
  obtain ⟨bound,wordEq⟩ := tail 0 (by simp)
  have addressPosition : address.val = (Compiler.encodeValues front).length := by simpa only [Compiler.encode_values_length] using addressSlot
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
  intro success
  split at effect
  · exact ⟨_,atBound,effect.2⟩
  · rw [effect] at success
    contradiction
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Load Step Footprint -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
 theorem step_load_footprint {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : SourceMachine.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Compiler.slots (f.locals.map Compiler.valueType) + Compiler.slots (front.map Compiler.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.memoryLoadInstruction op address address offset))
    (pcBound : raw.pc.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () → ∃ word, raw.base.val+address.val < exec.slots.length ∧
        out.2.1.slots.val = exec.slots.val.set (raw.base.val+address.val) word ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Compiler.memoryLoadInstruction op address address offset) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  have actualValues : ValuesAt exec.slots.val raw.base.val ((f.locals++front) ++ [SourceMachine.integerVal .I32 bits]) := by
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have actualAddress : address.val = Compiler.slots ((f.locals++front).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append] using addressSlot
  have handler := execute_load_footprint memory view laws {exec with frames := exec.frames.set index {raw with pc := pc}} store raw.instance raw.base op address offset inst memoryAddress object (f.locals++front) bits found mapped issued actualValues actualAddress bitsBound
  apply WP.spec_mono (dispatch_load memory hooks floats allocator _ store platform index raw.instance raw.function raw.base op address address offset handler)
  intro out effect success
  obtain ⟨word,bound,footprint⟩ := effect.1 success
  exact ⟨word,bound,footprint.1⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end

end

/-! ## MemoryGrow -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Exact memory-grow operand marshalling and result-slot update. -/
theorem memory_grow_handler {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (amount : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (amountSlot : exec.slots.val[base.val+dst.val]? = some amount)
    (post : U32 × runtime.store.Store M → Prop)
    (grown : runtime.store.Store.grow_memory_index memory store address.index (UScalar.cast .U32 amount) ⦃ post ⦄) :
    runtime.interp.execute_memory_grow memory exec store instanceIndex base dst ⦃ out =>
      ∃ result, out.1 = .Ok () ∧ post (result,out.2.2) ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ⦄ := by
  have amountBound := (List.getElem?_eq_some_iff.mp amountSlot).1
  unfold runtime.interp.execute_memory_grow
  rw [alloc.vec.Vec.index_slice_index]
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,instEq⟩
  subst actual
  step with vec_index_given inst.memories 0#usize address mapped as ⟨actual,addressEq⟩
  subst actual
  simp only [lift,bind_ok]
  step as ⟨slot,slotEq⟩
  have slotValue : slot.val = base.val+dst.val := by simpa only [U32.cast_Usize_val_eq] using slotEq
  step with vec_index_given exec.slots slot amount (by simpa only [slotValue] using amountSlot) as ⟨word,wordEq⟩
  subst word
  step with grown as ⟨result,nextStore,growth⟩
  step* <;> simp_all [SlotsEffect]
  exact ⟨result,growth,rfl⟩
end Itasca.Runtime.Interp

end
