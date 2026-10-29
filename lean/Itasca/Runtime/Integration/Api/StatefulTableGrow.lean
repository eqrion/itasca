import Itasca.Runtime.Integration.Api.StatefulGrowthChoice
import Itasca.Runtime.Interp.State.TableGrow
import Itasca.Runtime.Store.Api.TableGrowSource
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem stateful_table_growth {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (table : U32) (address : runtime.TableAddr)
    (object : runtime.store.TableInst) (delta : U32) (reference : U64) (out : U32 × runtime.store.Store M)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[val_ref (decodeRef object.ty reference),Abs.integerVal .I32 delta.val])
    (effect : TableGrowth store address.index delta reference out) :
    FrameStoreMetadata store out.2 ∧
    Abs.Stateful.Transition state f rest after (.tableGrow table.val)
      (Abs.advance {state with store:=decodeStore view code out.2}
        {f with code:=after,vals:=front++[Abs.integerVal .I32 out.1.val]} rest) := by
  have sourceMapped : f.module.TABLES[table.val]? = some address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem?_map,mapped]
  have sourceFound : state.store.TABLES[address.index.val]? = some (decodeTable object) := by
    simp [sourceStore,decodeStore,List.getElem?_map,issued]
  have decoded : Abs.integer .I32 (Abs.integerVal .I32 delta.val)=some delta.val :=
    Abs.integer_accepts .I32 _ (by change delta.val<2^32;scalar_tac)
  have splitValues : f.vals = (front++[val_ref (decodeRef object.ty reference)])++[Abs.integerVal .I32 delta.val] := by
    simpa only [List.append_assoc,List.singleton_append] using values
  rcases effect with ⟨failed,same⟩ | ⟨old,elements,count,lookup,words,capacity,used,limit,maximum,changed⟩
  · refine ⟨by rw [same];exact .refl _,{},Abs.Stateful.Selection.refusal_allowed _ _ _,?_⟩
    rw [failed,same,←sourceStore]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.tableGrow,splitValues,Abs.pop_append,sourceMapped,sourceFound,
      decoded,Abs.Stateful.asReference_value]
    rfl
  · have oldEq : old=object := Option.some.inj (lookup.symm.trans issued)
    subst old
    have grown := decode_table_growth object elements delta reference words capacity maximum
    have actual : decodeStore view code out.2 =
        {state.store with TABLES:=state.store.TABLES.set address.index.val (decodeTable {object with elements})} := by
      rw [changed,sourceStore]
      simp only [decodeStore,alloc.vec.Vec.set_val_eq,List.map_set]
      rfl
    have size : out.1.val=object.elements.length := by
      rw [changed]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      change object.elements.length < 2^32
      scalar_tac
    refine ⟨by rw [changed];exact ⟨rfl,rfl,rfl,rfl⟩,
      {table:=some (decodeTable {object with elements})},
      stateful_table_choice state f front table.val delta.val address.index.val _ _ _ values sourceMapped sourceFound (.grown grown),?_⟩
    rw [actual,size]
    simp only [Abs.Stateful.evaluate,Abs.Stateful.tableGrow,splitValues,Abs.pop_append,sourceMapped,sourceFound,
      decoded,Abs.Stateful.asReference_value]
    simp only [decodeTable,List.length_map]

theorem stateful_table_grow_effect {M A : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (reference amount : U64)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (referenceSlot : exec.slots.val[base.val+dst.val]? = some reference)
    (amountSlot : exec.slots.val[base.val+dst.val+1]? = some amount)
    (sizes : ∀ object ∈ store.tables.val, object.elements.length ≤ U32.max)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[val_ref (decodeRef object.ty reference),Abs.integerVal .I32 (UScalar.cast .U32 amount).val]) :
    runtime.interp.execute_table_grow memory allocator exec store instanceIndex base dst table ⦃ out =>
      out.1 = .Ok () ∧ FrameStoreMetadata store out.2.2 ∧ ∃ result : U32,
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ∧
        TableGrowth store address.index (UScalar.cast .U32 amount) reference (result,out.2.2) ∧
        Abs.Stateful.Transition state f rest after (.tableGrow table.val)
          (Abs.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  have primitive := table_grow_effect memory allocator allocation store address.index (UScalar.cast .U32 amount) reference
    (List.getElem?_eq_some_iff.mp issued).1 sizes
  apply WP.spec_mono (table_grow_handler memory allocator exec store instanceIndex base dst table inst address reference amount
    found mapped referenceSlot amountSlot _ primitive)
  rintro out ⟨result,success,growth,slots⟩
  obtain ⟨metadata,transition⟩ := stateful_table_growth view code store inst table address object (UScalar.cast .U32 amount) reference
    (result,out.2.2) state f rest after front mapped issued sourceStore moduleEq values growth
  exact ⟨success,metadata,result,slots,growth,transition⟩
end Itasca.Runtime.Theorems
