import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Store.Api.TableCopyPreservation
import Exec.Store.Api.TableCopySemantics
import Exec.Theorems.Composition.Certified.CertifiedCoreSegments
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem table_copy_core_certified {M : Type} (memoryOps : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (operand entry tableId sourceId : U32) (sourceAddress tableAddress : runtime.TableAddr)
    (table : runtime.store.TableInst) (sourceTable : runtime.store.TableInst) (destination source count : U64) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some compiled)
    (descriptor : compiled.indirect.val[entry.val]? = some (tableId,sourceId))
    (mapped : inst.tables.val[sourceId.val]? = some sourceAddress) (resolved : store.tables.val[sourceAddress.index.val]? = some sourceTable)
    (tableMapped : inst.tables.val[tableId.val]? = some tableAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (sameType : sourceTable.ty = table.ty) (moduleEq : ambient.MODULE = decodeInstance store inst)
    (certified : CertifiedCoreStore view code store) (ambientWf : wf_frame ambient) :
    runtime.interp.bulk.execute memoryOps store instIndex function base slots (.TableCopy operand entry) ⦃ out =>
      CertifiedCoreStore view code out.2 ∧ Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      FrameStoreMetadata store out.2 ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .TableOutOfBounds)) ∧
      StepsH ⟨⟨decodeStore view code store,ambient⟩,
        Spec.Segment.operands (bulkWord destination).val (bulkWord source).val (bulkWord count).val ++ [.TABLE_COPY (.mk_uN tableId.val) (.mk_uN sourceId.val)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ ∧
      (out.1 = .Err (.Trap .TableOutOfBounds) → out.2 = store) ⦄ := by
  apply WP.spec_mono (bulk_table_copy memoryOps store instIndex function base slots inst compiled operand entry tableId sourceId sourceAddress tableAddress table sourceTable
    destination source count found functionFound descriptor mapped resolved tableMapped target destinationSlot sourceSlot countSlot)
  intro out effect
  have metadata : SegmentObjectMetadata view store out.2 := effect.object_metadata target
  obtain ⟨fresh,extension⟩ := certified.segments metadata (effect.shape certified.shape target resolved sameType)
  have sourceSteps := effect.refines view code store inst ambient tableId sourceId tableAddress sourceAddress table sourceTable _ _ _ out
    moduleEq tableMapped mapped target resolved sameType certified.shape certified.storeSyntax ambientWf
    (by scalar_tac) (by scalar_tac) (by scalar_tac)
  refine ⟨fresh,extension,⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩,?_,sourceSteps,?_⟩
  all_goals
    unfold TableCopyEffect at effect
    split at effect
    · obtain ⟨words,rfl,values⟩ := effect
      first | exact Or.inl rfl | simp
    · rw [effect]
      first | exact Or.inr rfl | simp
end Exec.Theorems
