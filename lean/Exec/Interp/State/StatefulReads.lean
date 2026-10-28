import Exec.Interp.State.TableAccess
import Exec.Interp.Memory.MemorySize
import Exec.Abs.Stateful.Transition
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem stateful_table_size_effect (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (dstBound : base.val+dst.val < exec.slots.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst) :
    runtime.interp.execute_table_size memory exec store instanceIndex base dst table ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 object.elements.len)) ∧
      Abs.Stateful.Transition state f rest after (.tableSize table.val)
        (Abs.advance state {f with code := after,vals := f.vals++[Abs.integerVal .I32 object.elements.length]} rest) ⦄ := by
  apply WP.spec_mono (table_size_effect memory exec store instanceIndex base dst table inst address object found mapped issued dstBound)
  intro out effect
  refine ⟨effect.1,effect.2.1,effect.2.2,{},trivial,?_⟩
  simp [Abs.Stateful.evaluate,Abs.Stateful.tableSize,moduleEq,sourceStore,decodeInstance,decodeStore,
    List.getElem?_map,mapped,issued,decodeTable,alloc.vec.Vec.length]

theorem stateful_memory_size_effect (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : CodeInterpretation) (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (dstBound : base.val+dst.val < exec.slots.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst) :
    runtime.interp.execute_memory_size memory exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ pages : Usize,
        pages.val = (view object.buf).length / 65536 ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 pages)) ∧
        Abs.Stateful.Transition state f rest after .memorySize
          (Abs.advance state {f with code := after,vals := f.vals++[Abs.integerVal .I32 pages.val]} rest) ⦄ := by
  apply WP.spec_mono (memory_size_handler memory view laws exec store instanceIndex base dst inst address object found mapped issued dstBound)
  intro out effect
  obtain ⟨success,same,pages,pagesEq,slots⟩ := effect
  refine ⟨success,same,pages,pagesEq,slots,{},trivial,?_⟩
  simp [Abs.Stateful.evaluate,Abs.Stateful.memorySize,moduleEq,sourceStore,decodeInstance,decodeStore,
    List.getElem?_map,mapped,issued,decodeMemory,decodeBytes,pagesEq]

theorem stateful_table_get_effect (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst index table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (position : U32)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length) (dstBound : base.val+dst.val < exec.slots.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 position.val]) :
    runtime.interp.execute_table_get memory exec store instanceIndex base dst index table ⦃ out =>
      if position.val < object.elements.length then
        out.1 = .Ok () ∧ out.2.2 = store ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) object.elements.val[position.val]!) ∧
        Abs.Stateful.Transition state f rest after (.tableGet table.val)
          (Abs.advance state {f with code := after,vals := front++[val_ref (decodeRef object.ty object.elements.val[position.val]!)]} rest)
      else out = (.Err (.Trap .TableOutOfBounds),exec,store) ∧
        Abs.Stateful.Transition state f rest after (.tableGet table.val) .trap ⦄ := by
  have decoded : Abs.integer .I32 (Abs.integerVal .I32 position.val) = some position.val :=
    Abs.integer_accepts .I32 position.val (by change position.val < 2^32; scalar_tac)
  apply WP.spec_mono (table_get_effect memory exec store instanceIndex base dst index table inst address object position found mapped issued input indexBound dstBound)
  intro out effect
  by_cases inside : position.val < object.elements.length
  · simp only [inside,ite_true] at effect ⊢
    refine ⟨effect.1,effect.2.1,effect.2.2,{},trivial,?_⟩
    simp [Abs.Stateful.evaluate,Abs.Stateful.tableGet,values,Abs.pop_append,decoded,moduleEq,sourceStore,
      decodeInstance,decodeStore,List.getElem?_map,mapped,issued,decodeTable,inside,alloc.vec.Vec.length]
  · simp only [inside,ite_false] at effect ⊢
    refine ⟨effect,{},trivial,?_⟩
    simp [Abs.Stateful.evaluate,Abs.Stateful.tableGet,values,Abs.pop_append,decoded,moduleEq,sourceStore,
      decodeInstance,decodeStore,List.getElem?_map,mapped,issued,decodeTable,inside,alloc.vec.Vec.length]
end Itasca.Runtime.Interp
