import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryFullStore
import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryStoreEncoding
import Itasca.Runtime.Spec.SimdMemoryStore
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt
theorem full_store_source (address value : U128) (offset lane : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VSTORE .V128 argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val)
    (mapped : 0 < f.MODULE.MEMS.length) :
    runtime.interp.simd.memory_op 11#u32 offset lane address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val + offset.val + 16 ≤ bytes.length then
        out.1 = .Ok 0#u128 ∧ Store.decodeBytes out.2.val =
          (Store.decodeBytes bytes.val).setSlice! ((UScalar.cast .U32 address).val+offset.val) (vbytes_ .V128 (.mk_uN value.val)) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VCONST .V128 (.mk_uN value.val),.VSTORE .V128 argument]⟩ []
          ⟨⟨Spec.memoryPayloadWrite s f ((UScalar.cast .U32 address).val+offset.val) (vbytes_ .V128 (.mk_uN value.val)),f⟩,[]⟩
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VCONST .V128 (.mk_uN value.val),.VSTORE .V128 argument]⟩ []
          ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have source := Spec.Simd.full_store_step s f argument (UScalar.cast .U32 address).val value.bv
    storeWf frameWf (by scalar_tac) operationWf mapped
  simp only [memoryEq,offsetEq,Store.decodeBytes,List.length_map] at source
  apply WP.spec_mono (full_store_effect offset lane address value bytes)
  intro out effect
  unfold FullStoreEffect at effect
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + 16 ≤ bytes.val.length
  · rw [if_pos fits] at source effect ⊢
    obtain ⟨status,byteEffect⟩ := effect
    refine ⟨status,?_,source⟩
    rw [byteEffect,vectorStoreBytes_source bytes.val ((UScalar.cast .U32 address).val+offset.val) value (16) fits]
    rfl
  · rw [if_neg fits] at source effect ⊢
    exact ⟨effect,source⟩
end Itasca.Runtime.Interp.Simd
