import Exec.Theorems.Api.StatefulGrowthMatching
import Exec.Theorems.Api.GrowthChoiceMatching
import Exec.Theorems.Api.StatefulGrowthChoice
import Exec.Interp.State.TableGrow
import Exec.Store.Api.TableGrowSource
import Exec.Interp.Relations.FrameStoreMetadata
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem stateful_table_growth_chosen {choices : Exec.Spec.SourceChoices} (occurrence : Nat) {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (table : U32) (address : runtime.TableAddr)
    (object : runtime.store.TableInst) (delta : U32) (reference : U64) (out : U32 × runtime.store.Store M)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[val_ref (decodeRef object.ty reference),Abs.integerVal .I32 delta.val])
    (effect : TableGrowth store address.index delta reference out)
    (matched : choices.table occurrence (decodeTable object) delta.val (decodeRef object.ty reference)=tableGrowthReply address.index out) :
    FrameStoreMetadata store out.2 ∧
    Abs.Stateful.ChosenTransition choices occurrence state f rest after (.tableGrow table.val)
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
  · refine ⟨by rw [same];exact .refl _,{},Abs.Stateful.Selection.refusal_allowed _ _ _,?_,?_⟩
    · apply stateful_table_match choices occurrence state f front table.val delta.val address.index.val _ _ _ values sourceMapped sourceFound
      simpa only [tableGrowthReply,failed,show core.num.U32.MAX.val=2^32-1 by decide,ite_true] using matched
    · rw [failed,same,←sourceStore]
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
    by_cases sentinel : object.elements.length=2^32-1
    · have zero : delta.val=0 := by
        have bound := capacity
        have maximum32 : U32.max=4294967295 := by simp only [U32.max_eq]
        rw [maximum32,sentinel] at bound
        omega
      have unchanged : decodeStore view code out.2=state.store := by
        rw [actual]
        have objectEq : decodeTable {object with elements}=decodeTable object := by
          simp [decodeTable,words,zero]
        rw [objectEq]
        have replace : state.store.TABLES.set address.index.val (decodeTable object)=state.store.TABLES := by
          obtain ⟨bound,same⟩ := List.getElem?_eq_some_iff.mp sourceFound
          rw [←same,List.set_getElem_self]
        rw [replace]
      refine ⟨by rw [changed];exact ⟨rfl,rfl,rfl,rfl⟩,{},Abs.Stateful.Selection.refusal_allowed _ _ _,?_,?_⟩
      · apply stateful_table_match choices occurrence state f front table.val delta.val address.index.val _ _ _ values sourceMapped sourceFound
        simpa only [tableGrowthReply,size,sentinel,ite_true] using matched
      · rw [unchanged,size,sentinel]
        simp only [Abs.Stateful.evaluate,Abs.Stateful.tableGrow,splitValues,Abs.pop_append,sourceMapped,sourceFound,
          decoded,Abs.Stateful.asReference_value]
    · refine ⟨by rw [changed];exact ⟨rfl,rfl,rfl,rfl⟩,
        {table:=some (decodeTable {object with elements})},
        stateful_table_choice state f front table.val delta.val address.index.val _ _ _ values sourceMapped sourceFound (.grown grown),?_,?_⟩
      · apply stateful_table_match choices occurrence state f front table.val delta.val address.index.val _ _ _ values sourceMapped sourceFound
        rw [tableGrowthReply,if_neg (by simpa only [size] using sentinel)] at matched
        simpa [changed,alloc.vec.Vec.set_val_eq,List.getElem?_set,
          (List.getElem?_eq_some_iff.mp issued).1] using matched
      · rw [actual,size]
        simp only [Abs.Stateful.evaluate,Abs.Stateful.tableGrow,splitValues,Abs.pop_append,sourceMapped,sourceFound,
          decoded,Abs.Stateful.asReference_value]
        simp only [decodeTable,List.length_map]
end Exec.Theorems
