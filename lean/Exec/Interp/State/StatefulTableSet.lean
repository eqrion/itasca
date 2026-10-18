import Exec.Interp.State.TableMutation
import Exec.Abs.Stateful.Transition
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Store

theorem stateful_table_set_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (index value table : U32) (inst : runtime.store.Instance)
    (address : runtime.TableAddr) (object : runtime.store.Table) (position : U32)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length) (valueBound : base.val+value.val < exec.slots.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 position.val,val_ref (decodeRef object.ty exec.slots.val[base.val+value.val]!)]) :
    runtime.interp.admin_table_set memory hooks floats allocator exec store instanceIndex base index value table ⦃ out =>
      out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      if position.val < object.elements.length then
        out.1 = .Ok () ∧ TableMutation store out.2.2 address object exec.slots.val[base.val+value.val]! ∧
        Abs.Stateful.Transition state f rest after (.tableSet table.val)
          (Abs.advance {state with store := decodeStore view code out.2.2} {f with code := after,vals := front} rest)
      else out = (.Err (.Trap .TableOutOfBounds),exec,store) ∧
        Abs.Stateful.Transition state f rest after (.tableSet table.val) .trap ⦄ := by
  have decoded : Abs.integer .I32 (Abs.integerVal .I32 position.val) = some position.val :=
    Abs.integer_accepts .I32 position.val (by change position.val < 2^32; scalar_tac)
  have splitValues : f.vals = (front++[Abs.integerVal .I32 position.val])++[val_ref (decodeRef object.ty exec.slots.val[base.val+value.val]!)] := by
    simpa only [List.append_assoc,List.singleton_append] using values
  apply WP.spec_mono (table_set_effect memory hooks floats allocator exec store instanceIndex base index value table
    inst address object position found mapped issued input indexBound valueBound)
  intro out effect
  by_cases inside : position.val < object.elements.length
  · simp only [inside,ite_true] at effect ⊢
    rw [effect]
    refine ⟨rfl,⟨rfl,rfl,rfl,rfl⟩,rfl,?_,{},trivial,?_⟩
    · exact ⟨_,rfl,by simp,fun word member => List.mem_or_eq_of_mem_set (by simpa only [alloc.vec.Vec.set_val_eq] using member)⟩
    · have actual := table_write_decodes view code store inst f.toFrame table position address object
        exec.slots.val[base.val+value.val]! moduleEq mapped issued
      rw [actual]
      simp only [Abs.Stateful.evaluate,Abs.Stateful.tableSet,splitValues,Abs.pop_append,Abs.Stateful.asReference_value,decoded]
      simp [decoded,moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,issued,
        decodeTable,inside,alloc.vec.Vec.length]
  · simp only [inside,ite_false] at effect ⊢
    rw [effect]
    refine ⟨rfl,⟨rfl,rfl,rfl,rfl⟩,rfl,{},trivial,?_⟩
    simp only [Abs.Stateful.evaluate,Abs.Stateful.tableSet,splitValues,Abs.pop_append,Abs.Stateful.asReference_value,decoded]
    simp [decoded,moduleEq,sourceStore,decodeInstance,decodeStore,List.getElem?_map,mapped,issued,
      decodeTable,inside,alloc.vec.Vec.length]
end Exec.Interp
