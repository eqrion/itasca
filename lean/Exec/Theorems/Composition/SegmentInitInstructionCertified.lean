import Exec.Store.Initialization.BulkMemoryAt
import Exec.Store.Initialization.BulkTableAt
import Exec.Store.Api.MemoryInitSemantics
import Exec.Store.Api.TableInitSemantics
import Exec.Store.Initialization.SegmentObjectEffects
import Exec.Theorems.Composition.Certified.CertifiedCoreSegments
import Exec.Interp.Relations.FrameStoreMetadata
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem memory_init_core_certified {M : Type} (memoryOps : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memoryOps view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (operand data : U32) (address : Usize) (memoryAddress : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst) (destination source count : U64) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[data.val]? = some address) (resolved : store.datas.val[address.val]? = some segment)
    (memoryMapped : inst.memories.val[0]? = some memoryAddress)
    (target : store.memories.val[memoryAddress.index.val]? = some memory)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (certified : CertifiedCoreStore view code store) (ambientWf : wf_frame ambient) :
    runtime.interp.bulk.execute memoryOps store instIndex function base slots (.MemoryInit operand data) ⦃ out =>
      CertifiedCoreStore view code out.2 ∧ Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      FrameStoreMetadata store out.2 ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .MemoryOutOfBounds)) ∧
      StepsH ⟨⟨decodeStore view code store,ambient⟩,
        Spec.Segment.operands (bulkWord destination).val (bulkWord source).val (bulkWord count).val ++ [.MEMORY_INIT (.mk_uN data.val)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ ∧
      (out.1 = .Err (.Trap .MemoryOutOfBounds) → out.2 = store) ⦄ := by
  apply WP.spec_mono (bulk_memory_init_at memoryOps view laws store instIndex function base slots inst operand data address memoryAddress memory segment
    destination source count found mapped resolved memoryMapped target destinationSlot sourceSlot countSlot)
  intro out effect
  have metadata : SegmentObjectMetadata view store out.2 := effect.object_metadata target
  obtain ⟨fresh,extension⟩ := certified.segments metadata (effect.shape certified.shape target)
  have sourceSteps := effect.refines view code store inst ambient data memoryAddress address memory segment _ _ _ out
    moduleEq memoryMapped mapped target resolved certified.shape certified.storeSyntax ambientWf
    (certified.segmentBounds.data segment (List.mem_of_getElem? resolved)) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  refine ⟨fresh,extension,⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩,?_,sourceSteps,?_⟩
  all_goals
    unfold MemoryInitializationEffect at effect
    split at effect
    · obtain ⟨buffer,rfl,bytes⟩ := effect
      first | exact Or.inl rfl | simp
    · rw [effect]
      first | exact Or.inr rfl | simp

theorem table_init_core_certified {M : Type} (memoryOps : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (operand entry element tableId : U32) (address : Usize) (tableAddress : runtime.TableAddr)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst) (destination source count : U64) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some compiled)
    (descriptor : compiled.indirect.val[entry.val]? = some (element,tableId))
    (mapped : inst.elems.val[element.val]? = some address) (resolved : store.elems.val[address.val]? = some segment)
    (tableMapped : inst.tables.val[tableId.val]? = some tableAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (sameType : table.ty = segment.ty) (moduleEq : ambient.MODULE = decodeInstance store inst)
    (certified : CertifiedCoreStore view code store) (ambientWf : wf_frame ambient) :
    runtime.interp.bulk.execute memoryOps store instIndex function base slots (.TableInit operand entry) ⦃ out =>
      CertifiedCoreStore view code out.2 ∧ Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      FrameStoreMetadata store out.2 ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .TableOutOfBounds)) ∧
      StepsH ⟨⟨decodeStore view code store,ambient⟩,
        Spec.Segment.operands (bulkWord destination).val (bulkWord source).val (bulkWord count).val ++ [.TABLE_INIT (.mk_uN tableId.val) (.mk_uN element.val)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ ∧
      (out.1 = .Err (.Trap .TableOutOfBounds) → out.2 = store) ⦄ := by
  apply WP.spec_mono (bulk_table_init_at memoryOps store instIndex function base slots inst compiled operand entry element tableId address tableAddress table segment
    destination source count found functionFound descriptor mapped resolved tableMapped target destinationSlot sourceSlot countSlot)
  intro out effect
  have references : ∀ word ∈ segment.refs.val, ReferenceShape store table.ty word := by
    rw [sameType]
    exact certified.shape.elements segment (List.mem_of_getElem? resolved)
  have metadata : SegmentObjectMetadata view store out.2 := effect.object_metadata target
  obtain ⟨fresh,extension⟩ := certified.segments metadata (effect.shape certified.shape target references)
  have sourceSteps := effect.refines view code store inst ambient tableId element tableAddress address table segment _ _ _ out
    moduleEq tableMapped mapped target resolved sameType certified.shape certified.storeSyntax ambientWf
    (certified.segmentBounds.elements segment (List.mem_of_getElem? resolved)) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  refine ⟨fresh,extension,⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩,?_,sourceSteps,?_⟩
  all_goals
    unfold TableInitializationEffect at effect
    split at effect
    · obtain ⟨words,rfl,values⟩ := effect
      first | exact Or.inl rfl | simp
    · rw [effect]
      first | exact Or.inr rfl | simp
end Exec.Theorems
