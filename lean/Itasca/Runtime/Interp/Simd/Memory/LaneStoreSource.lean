import Itasca.Runtime.Interp.Simd.Memory.LaneBytes
import Itasca.Runtime.Interp.Simd.Memory.StoreEncoding
import Itasca.Runtime.Spec.Simd.MemoryLaneStore

/-!
Lane selection and source reduction for vector lane stores.

Main declarations: `memory_lane_selected` and `lane_store_source`. A direct consumer is `Interp.Simd.Memory.Relation`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins

theorem memory_lane_selected (ty : Jnn) (index : Nat) (before : BitVec 128)
    (valid : index < 128/lsize (lanetype_Jnn ty)) :
    (lanes_ (Spec.Simd.shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]! =
      .mk_lane__0 ty (.mk_uN (laneBits (lsize (lanetype_Jnn ty)) index before).toNat) := by
  simp only [lanes_,Spec.Simd.shapeOf,proj_uN_0,List.getElem!_eq_getElem?_getD,
    unpackLanes_getElem?,if_pos valid,Option.getD_some]
  rw [←lane_bits_to_nat]
  cases ty <;> rfl

theorem lane_store_source (ty : Jnn) (address value : U128) (offset index : U32) (bytes : Slice U8)
    (valid : index.val < 128/(shiftWidth ty).val)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index.val)))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val)
    (mapped : 0 < f.MODULE.MEMS.length) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty true) offset index address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
        out.1 = .Ok 0#u128 ∧ Store.decodeBytes out.2.val =
          (Store.decodeBytes bytes.val).setSlice! ((UScalar.cast .U32 address).val+offset.val)
            (integerBytes (memoryLaneBytes ty).val (laneBits (lsize (lanetype_Jnn ty)) index.val value.bv).toNat) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VCONST .V128 (.mk_uN value.val),
          .VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index.val)]⟩ []
          ⟨⟨Spec.memoryPayloadWrite s f ((UScalar.cast .U32 address).val+offset.val)
            (integerBytes (memoryLaneBytes ty).val (laneBits (lsize (lanetype_Jnn ty)) index.val value.bv).toNat),f⟩,[]⟩
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VCONST .V128 (.mk_uN value.val),
          .VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index.val)]⟩ []
          ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have valid' : index.val < 128/lsize (lanetype_Jnn ty) := by simpa only [shift_width_val] using valid
  have source := Spec.Simd.lane_store_step ty s f argument (UScalar.cast .U32 address).val index.val value.bv
    (laneBits (lsize (lanetype_Jnn ty)) index.val value.bv) valid' (memory_lane_selected _ _ _ valid')
    storeWf frameWf (by scalar_tac) operationWf mapped
  simp only [memoryEq,offsetEq,Store.decodeBytes,List.length_map,←memory_lane_bytes_val] at source
  apply WP.spec_mono (memory_lane_store_effect ty offset index address value bytes valid)
  intro out effect
  unfold LaneStoreEffect at effect
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · rw [if_pos fits] at source effect ⊢
    obtain ⟨word,bits,status,written⟩ := effect
    refine ⟨status,?_,source⟩
    rw [written,vector_store_bytes_source _ _ _ _ fits]
    have wordVal : word.val = (laneBits (lsize (lanetype_Jnn ty)) index.val value.bv).toNat := by
      have valueEq := congrArg BitVec.toNat bits
      rw [shift_width_val,BitVec.toNat_setWidth_of_le (by cases ty <;> decide)] at valueEq
      exact valueEq
    simp only [U64.cast_U128_val_eq,wordVal]
  · rw [if_neg fits] at source effect ⊢
    exact ⟨effect,source⟩
end Itasca.Runtime.Interp.Simd
