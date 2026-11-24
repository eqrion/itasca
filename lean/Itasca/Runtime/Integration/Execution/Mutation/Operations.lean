import Itasca.Runtime.Interp.State.ObjectBindingsAndMutation
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectBoundary
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Runtime.Interp.Calls.OutcomesAndResolution
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Machine.StateAndOwnership
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.Interp.Relations.EntryEffects
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Store.Api.AllocationAndGrowth
import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Interp.Memory.MemoryEffects
import Itasca.Runtime.Store.Api.BulkCopiesAndFill
import Itasca.Runtime.Store.Api.TableFillAndGrowth
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.Store.Invariant.CoreInstantiationSource
import Itasca.Runtime.Store.Initialization.SegmentInitializePreservation

open Itasca.Representation

/-!
# Store-mutation certificates

Typed table shape, exact concrete footprints and source extension combine into the cumulative mutation evidence consumed by execution.
-/

/-! ## TableShape -/

section TableShape

/-!
# Typed table mutation shape

Replacing table contents under the typing premises preserves decoded store shape and source extension. Joined mutation certificates use these facts.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Store Itasca.Interp

theorem table_mutation_shape {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) : Shape view after := by
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  obtain ⟨bound,found⟩ := List.getElem?_eq_some_iff.mp issued
  have old := shape.tables object (List.mem_of_getElem? issued)
  apply shape.table_replace_same_length address.index bound {object with elements := words}
  · refine ⟨by simpa only [lengthEq] using old.1,by simpa only [lengthEq] using old.2.1,?_⟩
    intro word member
    rcases references word member with previous | changed
    · exact old.2.2 word previous
    · simpa only [changed] using reference
  · simpa only [found] using lengthEq

/-- Typed table content replacement retains decoded store extension. -/
theorem table_mutation_extends {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before after : runtime.store.Store M)
    (shape : Shape view before) (syntaxProof : StoreSyntax code before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) :
    Shape view after ∧ Extend_store (decodeStore view code before) (decodeStore view code after) := by
  have fresh := table_mutation_shape view before after shape address object replacement issued mutation reference
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  obtain ⟨bound,found⟩ := List.getElem?_eq_some_iff.mp issued
  let after := {before with tables := before.tables.set address.index {object with elements := words}}
  have sourceSyntax : StoreSyntax code after := syntaxProof
  have oldWf := decode_store_wf view code before shape syntaxProof
  have newWf := decode_store_wf view code after fresh sourceSyntax
  have oldTableWf : wf_tableinst (decodeTable object) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decode_limits_wf _ _ (shape.tables object (List.mem_of_getElem? issued)).1
  have newTableWf : wf_tableinst (decodeTable {object with elements := words}) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    apply decode_limits_wf
    simpa only [lengthEq] using (shape.tables object (List.mem_of_getElem? issued)).1
  have objectExtension := decode_table_extends object {object with elements := words}
    rfl rfl (Nat.le_of_eq lengthEq.symm) oldTableWf newTableWf
  refine ⟨fresh,?_⟩
  unfold after at newWf
  rw [decode_store_table_update view code before (before.tables.set address.index {object with elements := words})] at newWf ⊢
  simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
  apply Spec.extend_store_set_table _ _ _ oldWf
  · simpa only [decodeStore] using newWf
  · intro indexBound
    simpa only [decodeStore,found,
      getElem!_pos (before.tables.val.map decodeTable) address.index.val
        (by simpa only [List.length_map] using bound),List.getElem_map] using objectExtension

end Itasca.Integration

end TableShape

/-! ## Operations -/

section Operations

/-!
# Joined store-mutation certificates

Exact growth footprints establish raw invariants; typed source transitions establish store extension. Their join constructs cumulative mutation evidence for concrete operations.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Store Itasca.Interp
theorem CumulativeStoreMutation.refl_of_shape {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {store : runtime.store.Store M}
    (shaped : Shape view store) (sourceSyntaxBefore : StoreSyntax code store) (bounds : SegmentBounds store) :
    CumulativeStoreMutation view code store store :=
  ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,shaped,bounds,Spec.extend_store_refl _ (decode_store_wf view code store shaped sourceSyntaxBefore),⟨rfl,rfl⟩,rfl⟩

theorem memory_mutation_cumulative_of_shape {M : Type} (view : M → Slice U8)
    (code : Representation.CodeInterpretation) (before after : runtime.store.Store M)
    (shaped : Shape view before) (sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (issued : before.memories.val[address.index.val]? = some object)
    (mutation : Interp.MemoryMutation view before after address object) :
    CumulativeStoreMutation view code before after := by
  obtain ⟨buffer,rfl,lengthEq⟩ := mutation
  have inBounds : address.index.val < before.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  have found : before.memories.val[address.index.val] = object := (List.getElem?_eq_some_iff.mp issued).2
  let after := {before with memories := before.memories.set address.index {object with buf := buffer}}
  have shape : Representation.Shape view after := by
    apply shaped.memory_replace_same_length address.index inBounds
    · simpa only [found] using lengthEq
    · simp only [found]
  have sourceSyntax : Store.StoreSyntax code after := sourceSyntaxBefore
  have oldWf := Store.decode_store_wf view code before shaped sourceSyntaxBefore
  have newWf := Store.decode_store_wf view code after shape sourceSyntax
  have oldMemoryWf : wf_meminst (Representation.decodeMemory view object) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply Store.decode_limits_wf
      have bound := (shaped.memories object (List.mem_of_getElem? issued)).2.1
      scalar_tac
    · exact Store.decode_bytes_wf _
  have newMemoryWf : wf_meminst (Representation.decodeMemory view {object with buf := buffer}) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply Store.decode_limits_wf
      have bound := (shaped.memories object (List.mem_of_getElem? issued)).2.1
      simp only [lengthEq]
      scalar_tac
    · exact Store.decode_bytes_wf _
  have objectExtension := Store.decode_memory_extends view object {object with buf := buffer}
    rfl (Nat.le_of_eq lengthEq.symm) oldMemoryWf newMemoryWf
  have extension : Extend_store (Representation.decodeStore view code before) (Representation.decodeStore view code after) := by
    unfold after at newWf ⊢
    rw [Representation.decode_store_memory_update view code before
      (before.memories.set address.index {object with buf := buffer})] at newWf ⊢
    simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
    apply Spec.extend_store_set_mem _ _ _ oldWf
    · simpa only [Representation.decodeStore] using newWf
    · intro bound
      simpa only [Representation.decodeStore,found,
        getElem!_pos (before.memories.val.map (Representation.decodeMemory view)) address.index.val
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
    (decode_store_wf view code before shaped sourceSyntaxBefore)
    (decode_store_wf view code after shape syntaxAfter)
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
    (code : Representation.CodeInterpretation) (before after : runtime.store.Store M)
    (shaped : Shape view before) (sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before) (value : val)
    (mutation : GlobalMutation before after value) (wellFormed : wf_val value)
    (owned : SourceMachine.Ownership.ValueOwned (ownershipBounds before) value) :
    CumulativeStoreMutation view code before after := by
  have shape := global_mutation_shape shaped mutation wellFormed owned
  obtain ⟨index,old,lo,hi,issued,mutable,typed,represented,high,rfl⟩ := mutation
  have sourceSyntax : StoreSyntax code {before with globals := before.globals.set index {old with lo,hi}} := sourceSyntaxBefore
  have oldWf := decode_store_wf view code before shaped sourceSyntaxBefore
  have newWf := decode_store_wf view code _ shape sourceSyntax
  have objectExtension : Extend_globalinst (decodeGlobal old) (decodeGlobal {old with lo,hi}) := by
    unfold decodeGlobal
    rw [mutable]
    exact Spec.extend_global_mutable _ _ _
      (.globalinst_case_ _ _ (decode_words_wf _ _ _))
      (.globalinst_case_ _ _ (decode_words_wf _ _ _))
  have extension : Extend_store (decodeStore view code before)
      (decodeStore view code {before with globals := before.globals.set index {old with lo,hi}}) := by
    rw [decode_store_global_update view code before (before.globals.set index {old with lo,hi})] at newWf ⊢
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
    (code : CodeInterpretation) (before after : runtime.store.Store M) (source : SourceMachine.AState)
    (shaped : Shape view before) (sourceSyntaxBefore : StoreSyntax code before) (bounds : SegmentBounds before)
    (owned : SourceMachine.Ownership.CoreOwned (ownershipBounds before) source)
    (mutation : CoreStoreMutation view source before after) : CumulativeStoreMutation view code before after := by
  cases mutation with
  | unchanged => exact .refl_of_shape shaped sourceSyntaxBefore bounds
  | memory issued mutation => exact memory_mutation_cumulative_of_shape view code before _ shaped sourceSyntaxBefore bounds _ _ issued mutation
  | global live wellFormed mutation => exact global_mutation_cumulative_of_shape view code before _ shaped sourceSyntaxBefore bounds _ mutation wellFormed (live.owned owned)
end Itasca.Integration

end Operations
