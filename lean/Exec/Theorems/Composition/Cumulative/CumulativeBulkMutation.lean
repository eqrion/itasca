import Exec.Theorems.Composition.Cumulative.CumulativeMutationEffects
import Exec.Store.Api.MemoryFillMutation
import Exec.Store.Api.TableFillMutation
import Exec.Store.Api.MemoryCopyMutation
import Exec.Store.Api.TableCopyPreservation
import Exec.Store.Initialization.SegmentObjectEffects
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem memory_fill_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.MemoryAddr} {object destination count value out}
    (certified : CertifiedCumulativeStore view code store)
    (issued : store.memories.val[address.index.val]? = some object)
    (effect : MemoryFillEffect view store address.index object destination count value out) :
    CumulativeStoreMutation view code store out.2 := by
  rcases (effect.mutation view store address object destination count value out).2 with ⟨_,mutation⟩ | ⟨_,same⟩
  · exact memory_mutation_cumulative view code store out.2 certified address object issued mutation
  · rw [same]; exact .refl certified

theorem memory_copy_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.MemoryAddr} {object destination source count out}
    (certified : CertifiedCumulativeStore view code store)
    (issued : store.memories.val[address.index.val]? = some object)
    (effect : MemoryCopyEffect view store address.index object destination source count out) :
    CumulativeStoreMutation view code store out.2 := by
  rcases (effect.mutation view store address object destination source count out).2 with ⟨_,mutation⟩ | ⟨_,same⟩
  · exact memory_mutation_cumulative view code store out.2 certified address object issued mutation
  · rw [same]; exact .refl certified

theorem table_fill_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.TableAddr} {object destination value count out}
    (certified : CertifiedCumulativeStore view code store)
    (issued : store.tables.val[address.index.val]? = some object)
    (reference : ReferenceShape store object.ty value)
    (effect : TableFillEffect store address.index object destination value count out) :
    CumulativeStoreMutation view code store out.2 := by
  rcases (effect.mutation store address object destination value count out).2 with ⟨_,mutation⟩ | ⟨_,same⟩
  · exact table_mutation_cumulative view code store out.2 certified address object value issued mutation reference
  · rw [same]; exact .refl certified

theorem table_copy_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index sourceIndex : Usize} {object sourceObject destination source count out}
    (certified : CertifiedCumulativeStore view code store)
    (issued : store.tables.val[index.val]? = some object)
    (sourceFound : store.tables.val[sourceIndex.val]? = some sourceObject)
    (sameType : sourceObject.ty = object.ty)
    (effect : TableCopyEffect store index object sourceObject destination source count out) :
    CumulativeStoreMutation view code store out.2 :=
  segment_mutation_cumulative certified (effect.object_metadata issued)
    (effect.shape certified.shape issued sourceFound sameType)

theorem memory_init_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index : Usize} {object segment destination source count out}
    (certified : CertifiedCumulativeStore view code store)
    (issued : store.memories.val[index.val]? = some object)
    (effect : MemoryInitializationEffect view store index object segment destination source count out) :
    CumulativeStoreMutation view code store out.2 :=
  segment_mutation_cumulative certified (effect.object_metadata issued) (effect.shape certified.shape issued)

theorem table_init_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index elementIndex : Usize} {object segment destination source count out}
    (certified : CertifiedCumulativeStore view code store)
    (issued : store.tables.val[index.val]? = some object)
    (sourceFound : store.elems.val[elementIndex.val]? = some segment)
    (sameType : segment.ty = object.ty)
    (effect : TableInitializationEffect store index object segment destination source count out) :
    CumulativeStoreMutation view code store out.2 := by
  apply segment_mutation_cumulative certified (effect.object_metadata issued)
  apply effect.shape certified.shape issued
  intro word member
  rw [←sameType]
  exact certified.shape.elements segment (List.mem_of_getElem? sourceFound) word member

theorem data_drop_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index : Usize} {object : runtime.store.DataInst}
    (certified : CertifiedCumulativeStore view code store)
    (issued : store.datas.val[index.val]? = some object) :
    CumulativeStoreMutation view code store {store with datas := store.datas.set index ⟨alloc.vec.Vec.new U8⟩} :=
  segment_mutation_cumulative certified (.data_drop view store index object issued) (certified.shape.data_drop index)

theorem element_drop_cumulative_mutation {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index : Usize} {object : runtime.store.ElemInst}
    (certified : CertifiedCumulativeStore view code store)
    (issued : store.elems.val[index.val]? = some object) :
    CumulativeStoreMutation view code store {store with elems := store.elems.set index {object with refs := alloc.vec.Vec.new U64}} :=
  segment_mutation_cumulative certified (.element_drop view store index object issued) (certified.shape.element_drop index object)
end Exec.Theorems
