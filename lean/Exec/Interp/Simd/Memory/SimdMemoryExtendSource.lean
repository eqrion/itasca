import Exec.Interp.Simd.Memory.SimdMemoryExtend
import Exec.Interp.Simd.Memory.SimdMemoryExtendBytes
import Exec.Spec.SimdMemoryExtend
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec.Simd

theorem extend_load_source (ty : WidenWidth) (signed : Bool) (address value : U128) (offset index : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (memoryExtendSource ty signed argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val) :
    runtime.interp.simd.memory_op (memoryExtendOpcode ty signed) offset index address value bytes ⦃ out =>
      out.2 = bytes ∧ match out.1 with
      | .Ok word => StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,
          memoryExtendSource ty signed argument]⟩ []
          ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN word.val)]⟩
      | .Err error => error = .Trap .MemoryOutOfBounds ∧
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,
            memoryExtendSource ty signed argument]⟩ []
            ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  apply WP.spec_mono (memory_extend_effect ty signed offset index address value bytes)
  intro out effect
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + 8 ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨answer,rfl,bits⟩ := effect
    refine ⟨rfl,?_⟩
    dsimp only
    apply Spec.Simd.extend_load_value ty signed s f argument (UScalar.cast .U32 address).val
      (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0 8).bv answer.bv
      storeWf frameWf (by scalar_tac) operationWf
    · intro j valid
      rw [memoryEq,offsetEq]
      exact vector_extend_load_bytes _ _ _ _ fits valid
    · exact bits
  · rw [if_neg fits] at effect
    rw [effect]
    refine ⟨rfl,rfl,?_⟩
    apply Spec.Simd.extend_load_trap ty signed s f argument (UScalar.cast .U32 address).val
      storeWf frameWf (by scalar_tac) operationWf
    simpa only [memoryEq,offsetEq,Store.decodeBytes,List.length_map] using Nat.lt_of_not_ge fits
end Itasca.Runtime.Interp.Simd
