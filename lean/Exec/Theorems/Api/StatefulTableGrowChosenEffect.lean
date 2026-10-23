import Exec.Theorems.Api.StatefulTableGrowthChosen
import Exec.Theorems.Api.GrowthChoiceMatching
import Exec.Interp.State.TableGrow
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem stateful_table_grow_effect_chosen {choices : Exec.Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
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
        Abs.Stateful.ChosenTransition choices occurrence state f rest after (.tableGrow table.val)
          (Abs.advance {state with store:=decodeStore view code out.2.2}
            {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest) ⦄ := by
  have primitive := table_grow_effect memory allocator allocation store address.index (UScalar.cast .U32 amount) reference
    (List.getElem?_eq_some_iff.mp issued).1 sizes
  have chosenPrimitive : runtime.store.Store.grow_table_index memory allocator store address.index (UScalar.cast .U32 amount) reference ⦃ out => TableGrowth store address.index (UScalar.cast .U32 amount) reference out ∧ choices.table occurrence (decodeTable object) (UScalar.cast .U32 amount).val (decodeRef object.ty reference)=tableGrowthReply address.index out ⦄ := by
    obtain ⟨out,actual,effect⟩ := WP.spec_imp_exists primitive
    rw [actual,WP.spec_ok]
    exact ⟨effect,compatible.tableReply occurrence store address.index (UScalar.cast .U32 amount) reference object out issued actual⟩
  apply WP.spec_mono (table_grow_handler memory allocator exec store instanceIndex base dst table inst address reference amount
    found mapped referenceSlot amountSlot _ chosenPrimitive)
  rintro out ⟨result,success,⟨growth,matched⟩,slots⟩
  obtain ⟨metadata,transition⟩ := stateful_table_growth_chosen occurrence view code store inst table address object (UScalar.cast .U32 amount) reference
    (result,out.2.2) state f rest after front mapped issued sourceStore moduleEq values growth matched
  exact ⟨success,metadata,result,slots,growth,transition⟩
end Exec.Theorems
