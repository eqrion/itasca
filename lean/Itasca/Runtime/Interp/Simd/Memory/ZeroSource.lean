import Itasca.Runtime.Interp.Simd.Memory.LoadSource
import Itasca.Runtime.Spec.Simd.MemoryZero

/-!
Source reduction for zero-extending vector loads.

Main declarations: `zero_load_source`. A direct consumer is `Interp.Simd.Memory.Relation`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt
theorem zero_load_source (op : PlainLoad) (zero : op ≠ .full) (address value : U128) (offset lane : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val) :
    runtime.interp.simd.memory_op op.opcode offset lane address value bytes ⦃ out =>
      out.2 = bytes ∧ match out.1 with
      | .Ok word => StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument]⟩ []
          ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN word.val)]⟩
      | .Err error => error = .Trap .MemoryOutOfBounds ∧
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument]⟩ []
            ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have supported : op.bytes.val*8 = 32 ∨ op.bytes.val*8 = 64 := by
    cases op <;> simp_all [PlainLoad.bytes]
  have byteCount : op.bytes.val*8/8 = op.bytes.val := by omega
  have source := Spec.Simd.zero_load_step (op.bytes.val*8) supported s f argument (UScalar.cast .U32 address).val
    storeWf frameWf (by scalar_tac) operationWf (by rw [memoryEq]; exact memory_bytes_wf bytes.val)
  simp only [Spec.Simd.zeroLoadResult,byteCount,memoryEq,offsetEq,Store.decodeBytes,List.length_map] at source
  apply WP.spec_mono (plain_load_effect op offset lane address value bytes)
  intro out effect
  change (if (UScalar.cast .U32 address).val + offset.val + op.bytes.val ≤ bytes.length then
    out = (.Ok (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val + offset.val) 0#u128 0 op.bytes.val),bytes)
    else out = (.Err (.Trap .MemoryOutOfBounds),bytes)) at effect
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + op.bytes.val ≤ bytes.val.length
  · rw [if_pos fits] at source effect
    rw [effect]
    refine ⟨rfl,?_⟩
    dsimp only
    rw [vector_load_bytes_source _ _ _ op.small fits]
    simpa only [inv_vbytes_,inv_ibytes_,Store.decodeBytes,List.map_take,List.map_drop] using source
  · rw [if_neg fits] at source effect
    rw [effect]
    exact ⟨rfl,rfl,source⟩
end Itasca.Runtime.Interp.Simd
