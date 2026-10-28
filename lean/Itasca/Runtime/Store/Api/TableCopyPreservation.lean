import Itasca.Runtime.Store.Api.TableCopyEffect
import Itasca.Runtime.Store.Initialization.BulkPreservation
import Itasca.Runtime.Store.Initialization.SegmentObjectEffects
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Copy has the same payload-preserving effect as initialization from an
immutable snapshot of the source table. This is only a proof view. -/
theorem TableCopyEffect.initialization {M : Type} {store : runtime.store.Store M}
    {index table sourceTable destination source count out}
    (effect : TableCopyEffect store index table sourceTable destination source count out) :
    TableInitializationEffect store index table ⟨sourceTable.ty,sourceTable.elements⟩ destination source count out := by
  unfold TableCopyEffect at effect
  unfold TableInitializationEffect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,values⟩ := effect
    simp only [inside,and_self,↓reduceIte]
    refine ⟨words,rfl,?_⟩
    rw [values,copySegment_eq_copyInto,Spec.Segment.copyInto_eq_setSlice _ _ _ _ _ inside.2 inside.1]
  · rename_i outside
    simp only [outside,↓reduceIte]
    exact effect

theorem TableCopyEffect.shape {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {sourceIndex : Usize} {index table sourceTable destination source count out}
    (effect : TableCopyEffect store index table sourceTable destination source count out)
    (shape : Shape view store) (target : store.tables.val[index.val]? = some table)
    (sourceFound : store.tables.val[sourceIndex.val]? = some sourceTable)
    (sameType : sourceTable.ty=table.ty) : Shape view out.2 := by
  apply effect.initialization.shape shape target
  intro word member
  rw [←sameType]
  exact (shape.tables sourceTable (List.mem_of_getElem? sourceFound)).2.2 word member

theorem TableCopyEffect.object_metadata {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {index table sourceTable destination source count out}
    (effect : TableCopyEffect store index table sourceTable destination source count out)
    (target : store.tables.val[index.val]? = some table) : SegmentObjectMetadata view store out.2 :=
  effect.initialization.object_metadata target
end Itasca.Runtime.Store
