import Itasca.Runtime.Interp.Simd.Relations.ValueSlots
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Interp.Simd.Execution.FrameCapacity
import Itasca.Runtime.Interp.Relations.FrameStack
import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormed

/-!
Slot-prefix retention and issued-memory/capacity facts for SIMD frames.

Main declarations: `SlotPrefix.simd_result` and `FrameProgram.simd_capacity`. A direct consumer is `Interp.Machine.Simd.ConstantFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem SlotPrefix.simd_result (base : Nat) (words : List U64) (position : Nat)
    (width : U32) (value : U128) (above : base ≤ position) :
    SlotPrefix base words (simdResultSlots words position width value) := by
  unfold simdResultSlots
  split <;> split
  all_goals first
    | exact .refl _ _
    | exact .set _ _ _ _ above
    | exact .set _ _ _ _ (by omega)
    | exact (SlotPrefix.set _ _ _ _ above).trans (.set _ _ _ _ (by omega))

theorem module_memories_issued {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C) :
    ∀ address, inst.memories.val[0]? = some address →
      ∃ object, store.memories.val[address.index.val]? = some object := by
  intro address mapped
  have bound := (List.getElem?_eq_some_iff.mp mapped).1
  have sourceBound : 0 < (Store.decodeInstance store inst).MEMS.length := by
    simpa only [Store.decodeInstance,List.length_map] using bound
  have contextBound : 0 < C.MEMS.length := by rw [←bindings.mems.length_eq]; exact sourceBound
  obtain ⟨other,object,otherMapped,found⟩ := Stateful.memory_binding_raw view code store inst C C.MEMS[0]
    bindings (List.getElem?_eq_getElem contextBound)
  have same : other = address := Option.some.inj (otherMapped.symm.trans mapped)
  exact ⟨object,same ▸ found⟩

theorem FrameProgram.simd_capacity {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions} (program : FrameProgram store raw compiled locals results functions)
    (slots : Slice U64) (allocated : raw.base.val + compiled.slot_count.val ≤ slots.length)
    (instruction : runtime.bytecode.Instr) (opcode operand entry wa wb wc wr : U32)
    (fetch : compiled.code.val[raw.pc.val]? = some instruction)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (opcode,operand,operand,entry)))
    (shape : runtime.bytecode.simd_shape opcode = .ok (some (wa,wb,wc,wr))) :
    raw.base.val + operand.val + wa.val + wb.val ≤ Usize.max ∧
    (wc = 2#u32 → raw.base.val + operand.val + wa.val + wb.val < Usize.max) ∧
    raw.base.val + operand.val + wr.val ≤ slots.length := by
  obtain ⟨input,output,_⟩ := Compiler.simd_valid_bounds compiled instruction opcode operand operand entry wa wb wc wr
    view shape (Compiler.well_formed_fetched compiled program.checked raw.pc.val instruction fetch)
  exact simd_frame_capacity slots raw.base compiled.slot_count operand operand wa wb wc wr allocated input output

end Itasca.Runtime.Interp
