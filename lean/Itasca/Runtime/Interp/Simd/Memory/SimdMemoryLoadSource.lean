import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryPlain
import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryEncoding
import Itasca.Runtime.Spec.SimdMemoryLoad
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt

theorem memory_bytes_wf (bytes : List U8) : Forall wf_byte (Store.decodeBytes bytes) := by
  intro byte member
  obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
  constructor
  scalar_tac

theorem full_load_source (address value : U128) (offset lane : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VLOAD .V128 none argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val) :
    runtime.interp.simd.memory_op 0#u32 offset lane address value bytes ⦃ out =>
      out.2 = bytes ∧ match out.1 with
      | .Ok word => StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VLOAD .V128 none argument]⟩ []
          ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN word.val)]⟩
      | .Err error => error = .Trap .MemoryOutOfBounds ∧
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VLOAD .V128 none argument]⟩ []
            ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have source := Spec.Simd.full_load_step s f argument (UScalar.cast .U32 address).val
    storeWf frameWf (by scalar_tac) operationWf (by rw [memoryEq]; exact memory_bytes_wf bytes.val)
  simp only [Spec.Simd.fullLoadResult,memoryEq,offsetEq,Store.decodeBytes,List.length_map] at source
  apply WP.spec_mono (plain_load_effect .full offset lane address value bytes)
  intro out effect
  change (if (UScalar.cast .U32 address).val + offset.val + 16 ≤ bytes.length then
    out = (.Ok (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val + offset.val) 0#u128 0 16),bytes)
    else out = (.Err (.Trap .MemoryOutOfBounds),bytes)) at effect
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + 16 ≤ bytes.val.length
  · rw [if_pos fits] at source effect
    rw [effect]
    refine ⟨rfl,?_⟩
    dsimp only
    rw [vectorLoadBytes_source _ _ _ (by decide) fits]
    simpa only [inv_vbytes_,inv_ibytes_,Store.decodeBytes,List.map_take,List.map_drop] using source
  · rw [if_neg fits] at source effect
    rw [effect]
    exact ⟨rfl,rfl,source⟩
end Itasca.Runtime.Interp.Simd
