import Exec.Store.Api.GrowthLimits
import Exec.Theorems.Composition.Cumulative.CumulativeMutationCertified
import Exec.Theorems.Composition.TableInstructionCertified
import Exec.Interp.Memory.MemoryMutation
import Exec.Store.Invariant.ObjectExtension
import Exec.Store.Api.GrowthEffects
import Exec.Store.Api.MemoryFillMutation
import Exec.Store.Api.TableFillMutation
import Exec.Store.Api.MemoryCopyMutation
import Exec.Store.Api.TableCopyPreservation
import Exec.Store.Initialization.SegmentObjectEffects
import Exec.Store.Invariant.SemanticApi
import Exec.Store.Invariant.Syntax
import Exec.Spec.Mutation
import Exec.Interp.Core.Mutation
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.Core
import Exec.Theorems.Composition.Core.CoreContents
import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Abs.ModuleBindingsExtension
import Exec.Theorems.Composition.GlobalMutationShape
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Store.Initialization.SegmentExtension
import Exec.Store.Invariant.SourceSyntax
import Exec.Store.Initialization.SegmentInitializeMetadata
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp
theorem CumulativeStoreMutation.refl_of_shape {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {store : runtime.store.Store M}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store) :
    CumulativeStoreMutation view code store store :=
  ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,shaped,bounds,Spec.extend_store_refl _ (decodeStore_wf view code store shaped sourceSyntaxBefore),⟨rfl,rfl⟩,rfl⟩

theorem memory_mutation_cumulative_of_shape {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M)
    (shaped : Shape view before) (sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (issued : before.memories.val[address.index.val]? = some object)
    (mutation : Interp.MemoryMutation view before after address object) :
    CumulativeStoreMutation view code before after := by
  obtain ⟨buffer,rfl,lengthEq⟩ := mutation
  have inBounds : address.index.val < before.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  have found : before.memories.val[address.index.val] = object := (List.getElem?_eq_some_iff.mp issued).2
  let after := {before with memories := before.memories.set address.index {object with buf := buffer}}
  have shape : Store.Shape view after := by
    apply shaped.memory_replace_same_length address.index inBounds
    · simpa only [found] using lengthEq
    · simp only [found]
  have sourceSyntax : Store.StoreSyntax code after := sourceSyntaxBefore
  have oldWf := Store.decodeStore_wf view code before shaped sourceSyntaxBefore
  have newWf := Store.decodeStore_wf view code after shape sourceSyntax
  have oldMemoryWf : wf_meminst (Store.decodeMemory view object) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply Store.decodeLimits_wf
      have bound := (shaped.memories object (List.mem_of_getElem? issued)).2.1
      scalar_tac
    · exact Store.decodeBytes_wf _
  have newMemoryWf : wf_meminst (Store.decodeMemory view {object with buf := buffer}) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply Store.decodeLimits_wf
      have bound := (shaped.memories object (List.mem_of_getElem? issued)).2.1
      simp only [lengthEq]
      scalar_tac
    · exact Store.decodeBytes_wf _
  have objectExtension := Store.decodeMemory_extends view object {object with buf := buffer}
    rfl (Nat.le_of_eq lengthEq.symm) oldMemoryWf newMemoryWf
  have extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
    unfold after at newWf ⊢
    rw [Store.decodeStore_memory_update view code before
      (before.memories.set address.index {object with buf := buffer})] at newWf ⊢
    simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
    apply Spec.extend_store_set_mem _ _ _ oldWf
    · simpa only [Store.decodeStore] using newWf
    · intro bound
      simpa only [Store.decodeStore,found,
        getElem!_pos (before.memories.val.map (Store.decodeMemory view)) address.index.val
          (by simpa only [List.length_map] using inBounds),List.getElem_map] using objectExtension
  exact ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,shape,⟨bounds.elements,bounds.data⟩,extension,⟨rfl,rfl⟩,rfl⟩
theorem table_mutation_cumulative_of_shape {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before after : runtime.store.Store M)
    (shaped : Shape view before) (sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) :
    CumulativeStoreMutation view code before after := by
  obtain ⟨shape,extension⟩ := table_mutation_extends view code before after shaped sourceSyntaxBefore
    address object replacement issued mutation reference
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  exact ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,shape,⟨bounds.elements,bounds.data⟩,extension,⟨rfl,rfl⟩,rfl⟩

theorem segment_mutation_cumulative_of_shape {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {before after : runtime.store.Store M}
    (shaped : Shape view before) (sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before)
    (metadata : SegmentObjectMetadata view before after) (shape : Shape view after) :
    CumulativeStoreMutation view code before after := by
  have syntaxAfter := sourceSyntaxBefore.instances_eq metadata.space.instances
  have extension := metadata.extends code
    (decodeStore_wf view code before shaped sourceSyntaxBefore)
    (decodeStore_wf view code after shape syntaxAfter)
  exact ⟨⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩,
    by rw [metadata.space.frozen],shape,metadata.segment_bounds bounds,extension,
    ⟨metadata.space.elements,metadata.space.datas⟩,by rw [metadata.space.frozen]⟩

/-- The exact growth footprint supplies raw invariants; the chosen typed source
transition supplies store extension at the execution join. -/
theorem memory_growth_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before : runtime.store.Store M} {index : Usize} {delta out}
    (shaped : Shape view before) (_sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before)
    (issued : index.val < before.memories.length)
    (effect : MemoryGrowth view code before index delta out)
    (extension : Extend_store (decodeStore view code before) (decodeStore view code out.2)) :
    CumulativeStoreMutation view code before out.2 := by
  obtain ⟨metadata,externs,elements,datas⟩ := effect.metadata
  exact ⟨metadata,externs,effect.shape view code before shaped index delta issued out,
    ⟨by simpa only [elements] using bounds.elements,
     by simpa only [datas] using bounds.data⟩,extension,⟨by rw [elements],by rw [datas]⟩,effect.limits⟩

theorem table_growth_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before : runtime.store.Store M} {index : Usize} {delta value out}
    (shaped : Shape view before) (_sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before)
    (issued : index.val < before.tables.length)
    (owned : ReferenceShape before (before.tables.val[index.val]).ty value)
    (effect : TableGrowth before index delta value out)
    (extension : Extend_store (decodeStore view code before) (decodeStore view code out.2)) :
    CumulativeStoreMutation view code before out.2 := by
  obtain ⟨metadata,externs,elements,datas⟩ := effect.metadata
  exact ⟨metadata,externs,effect.shape view before shaped index delta value issued owned out,
    ⟨by simpa only [elements] using bounds.elements,
     by simpa only [datas] using bounds.data⟩,extension,⟨by rw [elements],by rw [datas]⟩,effect.limits⟩

theorem memory_fill_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.MemoryAddr} {object destination count value out}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store)
    (issued : store.memories.val[address.index.val]? = some object)
    (effect : MemoryFillEffect view store address.index object destination count value out) :
    CumulativeStoreMutation view code store out.2 := by
  rcases (effect.mutation view store address object destination count value out).2 with ⟨_,mutation⟩ | ⟨_,same⟩
  · exact memory_mutation_cumulative_of_shape view code store out.2 shaped sourceSyntaxBefore bounds address object issued mutation
  · rw [same]; exact .refl_of_shape shaped sourceSyntaxBefore bounds

theorem memory_copy_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.MemoryAddr} {object destination source count out}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store)
    (issued : store.memories.val[address.index.val]? = some object)
    (effect : MemoryCopyEffect view store address.index object destination source count out) :
    CumulativeStoreMutation view code store out.2 := by
  rcases (effect.mutation view store address object destination source count out).2 with ⟨_,mutation⟩ | ⟨_,same⟩
  · exact memory_mutation_cumulative_of_shape view code store out.2 shaped sourceSyntaxBefore bounds address object issued mutation
  · rw [same]; exact .refl_of_shape shaped sourceSyntaxBefore bounds

theorem table_fill_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {address : runtime.TableAddr} {object destination value count out}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store)
    (issued : store.tables.val[address.index.val]? = some object)
    (reference : ReferenceShape store object.ty value)
    (effect : TableFillEffect store address.index object destination value count out) :
    CumulativeStoreMutation view code store out.2 := by
  rcases (effect.mutation store address object destination value count out).2 with ⟨_,mutation⟩ | ⟨_,same⟩
  · exact table_mutation_cumulative_of_shape view code store out.2 shaped sourceSyntaxBefore bounds address object value issued mutation reference
  · rw [same]; exact .refl_of_shape shaped sourceSyntaxBefore bounds

theorem table_copy_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index sourceIndex : Usize} {object sourceObject destination source count out}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store)
    (issued : store.tables.val[index.val]? = some object)
    (sourceFound : store.tables.val[sourceIndex.val]? = some sourceObject)
    (sameType : sourceObject.ty = object.ty)
    (effect : TableCopyEffect store index object sourceObject destination source count out) :
    CumulativeStoreMutation view code store out.2 :=
  segment_mutation_cumulative_of_shape shaped sourceSyntaxBefore bounds (effect.object_metadata issued)
    (effect.shape shaped issued sourceFound sameType)

theorem memory_init_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index : Usize} {object segment destination source count out}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store)
    (issued : store.memories.val[index.val]? = some object)
    (effect : MemoryInitializationEffect view store index object segment destination source count out) :
    CumulativeStoreMutation view code store out.2 :=
  segment_mutation_cumulative_of_shape shaped sourceSyntaxBefore bounds (effect.object_metadata issued) (effect.shape shaped issued)

theorem table_init_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index elementIndex : Usize} {object segment destination source count out}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store)
    (issued : store.tables.val[index.val]? = some object)
    (sourceFound : store.elems.val[elementIndex.val]? = some segment)
    (sameType : segment.ty = object.ty)
    (effect : TableInitializationEffect store index object segment destination source count out) :
    CumulativeStoreMutation view code store out.2 := by
  apply segment_mutation_cumulative_of_shape shaped sourceSyntaxBefore bounds (effect.object_metadata issued)
  apply effect.shape shaped issued
  intro word member
  rw [←sameType]
  exact shaped.elements segment (List.mem_of_getElem? sourceFound) word member

theorem data_drop_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index : Usize} {object : runtime.store.DataInst}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store)
    (issued : store.datas.val[index.val]? = some object) :
    CumulativeStoreMutation view code store {store with datas := store.datas.set index ⟨alloc.vec.Vec.new U8⟩} :=
  segment_mutation_cumulative_of_shape shaped sourceSyntaxBefore bounds (.data_drop view store index object issued) (shaped.data_drop index)

theorem element_drop_cumulative_mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {store : runtime.store.Store M} {index : Usize} {object : runtime.store.ElemInst}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store)
    (issued : store.elems.val[index.val]? = some object) :
    CumulativeStoreMutation view code store {store with elems := store.elems.set index {object with refs := alloc.vec.Vec.new U64}} :=
  segment_mutation_cumulative_of_shape shaped sourceSyntaxBefore bounds (.element_drop view store index object issued) (shaped.element_drop index object)

theorem global_mutation_cumulative_of_shape {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M)
    (shaped : Shape view before) (sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before) (value : val)
    (mutation : GlobalMutation before after value) (wellFormed : wf_val value)
    (owned : Abs.Ownership.ValueOwned (ownershipBounds before) value) :
    CumulativeStoreMutation view code before after := by
  have shape := global_mutation_shape shaped mutation wellFormed owned
  obtain ⟨index,old,lo,hi,issued,mutable,typed,represented,high,rfl⟩ := mutation
  have sourceSyntax : StoreSyntax code {before with globals := before.globals.set index {old with lo,hi}} := sourceSyntaxBefore
  have oldWf := decodeStore_wf view code before shaped sourceSyntaxBefore
  have newWf := decodeStore_wf view code _ shape sourceSyntax
  have objectExtension : Extend_globalinst (decodeGlobal old) (decodeGlobal {old with lo,hi}) := by
    unfold decodeGlobal
    rw [mutable]
    exact Spec.extend_global_mutable _ _ _
      (.globalinst_case_ _ _ (decodeWords_wf _ _ _))
      (.globalinst_case_ _ _ (decodeWords_wf _ _ _))
  have extension : Extend_store (decodeStore view code before)
      (decodeStore view code {before with globals := before.globals.set index {old with lo,hi}}) := by
    rw [decodeStore_global_update view code before (before.globals.set index {old with lo,hi})] at newWf ⊢
    simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
    apply Spec.extend_store_set_global _ _ _ oldWf
    · simpa only [decodeStore] using newWf
    · intro bound
      have position := (List.getElem?_eq_some_iff.mp issued).1
      have actual := (List.getElem?_eq_some_iff.mp issued).2
      simpa only [decodeStore,getElem!_pos (before.globals.val.map decodeGlobal) index.val
        (by simpa only [List.length_map] using position),List.getElem_map,actual] using objectExtension
  exact ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,shape,⟨bounds.elements,bounds.data⟩,extension,⟨rfl,rfl⟩,rfl⟩

theorem core_mutation_cumulative_of_shape {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before after : runtime.store.Store M) (source : Abs.AState)
    (shaped : Shape view before) (sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before)
    (owned : Abs.Ownership.CoreOwned (ownershipBounds before) source)
    (mutation : CoreStoreMutation view source before after) : CumulativeStoreMutation view code before after := by
  cases mutation with
  | unchanged => exact .refl_of_shape shaped sourceSyntaxBefore bounds
  | memory issued mutation => exact memory_mutation_cumulative_of_shape view code before _ shaped sourceSyntaxBefore bounds _ _ issued mutation
  | global live wellFormed mutation => exact global_mutation_cumulative_of_shape view code before _ shaped sourceSyntaxBefore bounds _ mutation wellFormed (live.owned owned)
end Itasca.Runtime.Theorems
