import Exec.Interp.Simd.Memory.SimdMemoryLaneBytes
import Exec.Spec.SimdMemoryLane
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt

theorem lane_load_source (ty : Jnn) (address value : U128) (offset index : U32) (bytes : Slice U8)
    (valid : index.val < 128/(shiftWidth ty).val)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index.val)))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty false) offset index address value bytes ⦃ out =>
      out.2 = bytes ∧ match out.1 with
      | .Ok word => StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,
          .VCONST .V128 (.mk_uN value.val),.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index.val)]⟩ []
          ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN word.val)]⟩
      | .Err error => error = .Trap .MemoryOutOfBounds ∧
          StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VCONST .V128 (.mk_uN value.val),
            .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index.val)]⟩ []
            ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  apply WP.spec_mono (memory_lane_load_effect ty offset index address value bytes valid)
  intro out effect
  unfold LaneLoadEffect at effect
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨answer,rfl,bits⟩ := effect
    refine ⟨rfl,?_⟩
    dsimp only
    apply Spec.Simd.lane_load_value ty s f argument (UScalar.cast .U32 address).val index.val value.bv answer.bv
      ((UScalar.cast .U64 (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0
        (memoryLaneBytes ty).val)).bv.setWidth (lsize (lanetype_Jnn ty)))
      storeWf frameWf (by scalar_tac) operationWf
    · rw [memoryEq,offsetEq]
      exact vector_lane_load_bytes _ _ _ fits
    · have packed := packLanes_write (lanetype_Jnn ty) index.val value.bv
        (UScalar.cast .U64 (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0
          (memoryLaneBytes ty).val)).bv (by simpa only [shiftWidth_val] using valid)
      rw [shiftWidth_val] at bits
      rw [bits]
      cases ty <;> exact packed
  · rw [if_neg fits] at effect
    rw [effect]
    refine ⟨rfl,rfl,?_⟩
    apply Spec.Simd.lane_load_trap ty s f argument (UScalar.cast .U32 address).val index.val value.bv
      storeWf frameWf (by scalar_tac) operationWf
    simpa only [memoryEq,offsetEq,Store.decodeBytes,List.length_map,←memoryLaneBytes_val] using Nat.lt_of_not_ge fits
end Itasca.Runtime.Interp.Simd
