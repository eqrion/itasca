import Exec.Store.Api.MemoryFillMutation
import Exec.Store.Api.MemoryFillSemantics
import Exec.Theorems.Composition.Core.CoreMemoryInstructionCertified
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

/-- memory.fill preserves the byte-length store invariant and follows the
source per-byte reduction, including its all-or-nothing bounds failure. -/
theorem memory_fill_core_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand : U32) (inst : runtime.store.Instance) (address : runtime.MemoryAddr)
    (object : runtime.store.Memory M) (destination value count : U64) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some object)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (certified : CertifiedCoreStore view code store)
    (ambientWf : wf_frame ambient) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.MemoryFill operand) ⦃ out =>
      CertifiedCoreStore view code out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      FrameStoreMetadata store out.2 ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .MemoryOutOfBounds)) ∧
      StepsH ⟨⟨decodeStore view code store,ambient⟩,
        Spec.Segment.operands (bulkWord destination).val (UScalar.cast .U32 value).val (bulkWord count).val ++ [.MEMORY_FILL]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ ∧
      (out.1 = .Err (.Trap .MemoryOutOfBounds) → out.2 = store) ⦄ := by
  apply WP.spec_mono (bulk_memory_fill memory view laws store instIndex function base slots operand inst address object destination value count
    found mapped target destinationSlot valueSlot countSlot)
  intro out effect
  have source := effect.refines view code store inst ambient address object _ _ (UScalar.cast .U32 value) out
    moduleEq mapped target certified.shape certified.storeSyntax ambientWf
    (by simp only [bulkWord,U32.cast_U64_val_eq]; scalar_tac)
    (by simp only [bulkWord,U32.cast_U64_val_eq]; scalar_tac)
  have changed := Exec.Store.MemoryFillEffect.mutation view store address object _ _ _ out effect
  rcases changed.2 with ⟨success,mutation⟩ | ⟨trap,unchanged⟩
  · obtain ⟨fresh,extension⟩ := memory_mutation_core_certified view code store out.2 certified address object target mutation
    exact ⟨fresh,extension,changed.1,Or.inl success,source,by simp [success]⟩
  · exact ⟨by simpa only [unchanged] using certified,
      by simpa only [unchanged] using Spec.extend_store_refl _ (decodeStore_wf view code store certified.shape certified.storeSyntax),
      changed.1,Or.inr trap,source,fun _ => unchanged⟩
end Exec.Theorems
