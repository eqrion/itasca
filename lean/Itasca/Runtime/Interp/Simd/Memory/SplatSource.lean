import Itasca.Runtime.Interp.Simd.Memory.Splat
import Itasca.Runtime.Spec.Simd.MemorySplat

/-!
Source reduction for vector splat loads.

Main declarations: `splat_load_source`. A direct consumer is `Interp.Simd.Memory.Relation`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt

theorem splat_load_source (ty : Jnn) (address value : U128) (offset index : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val) :
    runtime.interp.simd.memory_op (memorySplatOpcode ty) offset index address value bytes ⦃ out =>
      out.2 = bytes ∧ match out.1 with
      | .Ok word => StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,
          .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument]⟩ []
          ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN word.val)]⟩
      | .Err error => error = .Trap .MemoryOutOfBounds ∧
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,
            .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument]⟩ []
            ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  apply WP.spec_mono (memory_splat_effect ty offset index address value bytes)
  intro out effect
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨answer,rfl,bits⟩ := effect
    refine ⟨rfl,?_⟩
    dsimp only
    apply Spec.Simd.splat_load_value ty s f argument (UScalar.cast .U32 address).val answer.bv
      ((UScalar.cast .U64 (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0
        (memoryLaneBytes ty).val)).bv.setWidth (lsize (lanetype_Jnn ty)))
      storeWf frameWf (by scalar_tac) operationWf
    · rw [memoryEq,offsetEq]
      exact vector_lane_load_bytes _ _ _ fits
    · cases ty <;> exact bits
  · rw [if_neg fits] at effect
    rw [effect]
    refine ⟨rfl,rfl,?_⟩
    apply Spec.Simd.splat_load_trap ty s f argument (UScalar.cast .U32 address).val
      storeWf frameWf (by scalar_tac) operationWf
    simpa only [memoryEq,offsetEq,Store.decodeBytes,List.length_map,←memoryLaneBytes_val] using Nat.lt_of_not_ge fits
end Itasca.Runtime.Interp.Simd
