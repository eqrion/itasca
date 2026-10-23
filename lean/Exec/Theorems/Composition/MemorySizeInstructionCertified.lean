import Exec.Interp.Memory.MemorySize
import Exec.Interp.Memory.MemoryDecode
import Exec.Spec.MemorySize
import Exec.Theorems.Composition.Certified.CertifiedCore
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

/-- MEMORY_SIZE reports the exact decoded page count and preserves the store. -/
theorem memory_size_instruction_certified {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (ambient : frame)
    (certified : CertifiedCoreStore view code store)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (issued : store.memories.val[address.index.val]? = some object)
    (slotBound : base.val+dst.val < exec.slots.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst) (ambientWf : wf_frame ambient) :
    runtime.interp.execute_memory_size memory exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      ∃ word : U64, word.val = (view object.buf).length / 65536 ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) word) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,[.MEMORY_SIZE]⟩ []
          ⟨⟨decodeStore view code store,ambient⟩,[Spec.Segment.i32 word.val]⟩ ⦄ := by
  have objectShape := certified.shape.memories object (List.mem_of_getElem? issued)
  have sourceMemory := memory_lookup_decodes view code store inst ambient address object moduleEq mapped issued
  have source := Spec.memory_size_step (decodeStore view code store) ambient
    (decodeStore_wf view code store certified.shape certified.storeSyntax) ambientWf
    (by rw [sourceMemory]; simpa only [decodeMemory,decodeBytes,List.length_map] using objectShape.1)
    (by rw [sourceMemory]; simp only [decodeMemory,decodeBytes,List.length_map]; have bound := objectShape.2.1; scalar_tac)
  apply WP.spec_mono (memory_size_handler memory view laws exec store instanceIndex base dst inst address object
    found mapped issued slotBound)
  intro out effect
  obtain ⟨success,same,pages,pagesEq,slots⟩ := effect
  have wordEq : (UScalar.cast .U64 pages).val = (view object.buf).length / 65536 := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
    · exact pagesEq
    · have bound := objectShape.2.1
      change pages.val < 2^64
      omega
  refine ⟨success,same,UScalar.cast .U64 pages,wordEq,slots,?_⟩
  rw [wordEq]
  rw [sourceMemory] at source
  simpa only [decodeMemory,decodeBytes,List.length_map] using source
end Exec.Theorems
