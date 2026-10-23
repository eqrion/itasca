import Exec.Store.Api.TableFillMutation
import Exec.Store.Api.TableFillSemantics
import Exec.Theorems.Composition.TableInstructionCertified
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

/-- table.fill preserves the issued-reference store invariant and follows the
source per-element reduction, including its all-or-nothing bounds failure. -/
theorem table_fill_core_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand tableId : U32) (inst : runtime.store.ModuleInst) (address : runtime.TableAddr)
    (table : runtime.store.TableInst) (destination value count : U64) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.tables.val[tableId.val]? = some address)
    (target : store.tables.val[address.index.val]? = some table)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (certified : CertifiedCoreStore view code store)
    (reference : ReferenceShape store table.ty value) (ambientWf : wf_frame ambient) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableFill operand tableId) ⦃ out =>
      CertifiedCoreStore view code out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      FrameStoreMetadata store out.2 ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .TableOutOfBounds)) ∧
      StepsH ⟨⟨decodeStore view code store,ambient⟩,
        Spec.Segment.fillOperands (bulkWord destination).val (decodeRef table.ty value) (bulkWord count).val ++ [.TABLE_FILL (.mk_uN tableId.val)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ ∧
      (out.1 = .Err (.Trap .TableOutOfBounds) → out.2 = store) ⦄ := by
  apply WP.spec_mono (bulk_table_fill memory store instIndex function base slots operand tableId inst address table destination value count
    found mapped target destinationSlot valueSlot countSlot)
  intro out effect
  have source := effect.refines view code store inst ambient tableId address table _ value _ out
    moduleEq mapped target certified.shape certified.storeSyntax ambientWf
    (by simp only [bulkWord,U32.cast_U64_val_eq]; scalar_tac)
    (by simp only [bulkWord,U32.cast_U64_val_eq]; scalar_tac)
  have changed := Exec.Store.TableFillEffect.mutation store address table _ value _ out effect
  rcases changed.2 with ⟨success,mutation⟩ | ⟨trap,unchanged⟩
  · obtain ⟨fresh,extension⟩ := table_mutation_core_certified view code store out.2 certified address table value target mutation reference
    exact ⟨fresh,extension,changed.1,Or.inl success,source,by simp [success]⟩
  · exact ⟨by simpa only [unchanged] using certified,
      by simpa only [unchanged] using Spec.extend_store_refl _ (decodeStore_wf view code store certified.shape certified.storeSyntax),
      changed.1,Or.inr trap,source,fun _ => unchanged⟩
end Exec.Theorems
