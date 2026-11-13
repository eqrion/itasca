import Itasca.Runtime.Interp.Simd.Memory.ExtendSource
import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdSourceShape
import Itasca.Runtime.SourceMachine.Simd.MemoryTransition
import Itasca.Runtime.Interp.Simd.Relations.LaneRelation
import Itasca.Runtime.Interp.Simd.Relations.ShuffleRelation
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Memory.MemorySize
import Itasca.Runtime.Interp.Simd.Execution.PureUnary
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Interp.Simd.Relations.OperandsBounded

/-!
Sections, each formerly its own module: LaneSource, StoreEncoding, LaneStoreSource, Splat, SplatSource, StoreSource, ZeroSource, Relation, Transition, ValuesTransition, ChangeDecode, ExecuteEffect, ExecuteError.
-/

/-! ## LaneSource -/

section

/-!
Source reduction for vector lane loads.

Main declarations: `lane_load_source`. A direct consumer is `Interp.Simd.Memory.Relation`.
-/

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
    · have packed := pack_lanes_write (lanetype_Jnn ty) index.val value.bv
        (UScalar.cast .U64 (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0
          (memoryLaneBytes ty).val)).bv (by simpa only [shift_width_val] using valid)
      rw [shift_width_val] at bits
      rw [bits]
      cases ty <;> exact packed
  · rw [if_neg fits] at effect
    rw [effect]
    refine ⟨rfl,rfl,?_⟩
    apply Spec.Simd.lane_load_trap ty s f argument (UScalar.cast .U32 address).val index.val value.bv
      storeWf frameWf (by scalar_tac) operationWf
    simpa only [memoryEq,offsetEq,Store.decodeBytes,List.length_map,←memory_lane_bytes_val] using Nat.lt_of_not_ge fits
end Itasca.Runtime.Interp.Simd

end

/-! ## StoreEncoding -/

section

/-!
Byte encoding of vector-store payloads.

Main declarations: `vectorStorePayload`. A direct consumer is `Interp.Simd.Memory.LaneStoreSource`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def vectorStorePayload (value : U128) (width : Nat) : List U8 :=
  (List.range width).map (vectorStoreByte value)

private theorem vector_store_payload_at (value : U128) (width index : Nat) (inside : index < width) :
    (vectorStorePayload value width)[index]! = vectorStoreByte value index := by
  simp [vectorStorePayload,List.getElem!_eq_getElem?_getD,inside]

theorem vector_store_bytes_copy_into (bytes : List U8) (start : Nat) (value : U128) (width index count : Nat)
    (inside : index + count ≤ width) :
    vectorStoreBytes bytes start value index count =
      Spec.Segment.copyInto bytes (vectorStorePayload value width) (start+index) index count := by
  induction count generalizing bytes index with
  | zero => rfl
  | succ count ih =>
    simp only [vectorStoreBytes,Spec.Segment.copyInto]
    rw [vector_store_payload_at value width index (by omega)]
    simpa only [Nat.add_assoc] using ih (bytes.set (start+index) (vectorStoreByte value index)) (index+1) (by omega)

theorem vector_store_bytes_set_slice (bytes : List U8) (start : Nat) (value : U128) (width : Nat)
    (inside : start + width ≤ bytes.length) :
    vectorStoreBytes bytes start value 0 width = bytes.setSlice! start (vectorStorePayload value width) := by
  rw [vector_store_bytes_copy_into bytes start value width 0 width (by omega)]
  simp only [Nat.add_zero]
  rw [Spec.Segment.copy_into_eq_set_slice _ _ _ _ _ (by simp [vectorStorePayload]) inside]
  simp only [List.slice_zero_j, Nat.zero_add]
  rw [List.take_of_length_le (by simp [vectorStorePayload])]

private theorem integer_bytes_at (count value index : Nat) (inside : index < count) :
    (SpecExt.Builtins.integerBytes count value)[index]? = some (.mk_byte ((value / 256^index) % 256)) := by
  induction index generalizing count value with
  | zero => cases count <;> simp_all [SpecExt.Builtins.integerBytes]
  | succ index ih =>
    cases count with
    | zero => omega
    | succ count =>
      simpa only [SpecExt.Builtins.integerBytes,List.getElem?_cons_succ,Nat.pow_succ,
        Nat.div_div_eq_div_mul,Nat.mul_comm] using ih count (value/256) (by omega)

theorem vector_store_payload_source (value : U128) (width : Nat) :
    Store.decodeBytes (vectorStorePayload value width) = SpecExt.Builtins.integerBytes width value.val := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < width
  · rw [integer_bytes_at width value.val index inside]
    simp only [Store.decodeBytes,vectorStorePayload,List.getElem?_map]
    simp only [List.getElem?_range inside,Option.map_some]
    congr 2
    change (value.val >>> (index*8)) % 256 = (value.val / 256^index) % 256
    rw [Nat.shiftRight_eq_div_pow]
    congr 2
    rw [Nat.mul_comm, Nat.pow_mul]
  · have outside : width ≤ index := by omega
    rw [List.getElem?_eq_none (by simpa [Store.decodeBytes,vectorStorePayload] using outside),
      List.getElem?_eq_none (by simpa only [SpecExt.Builtins.integerBytes_length] using outside)]

theorem vector_store_bytes_source (bytes : List U8) (start : Nat) (value : U128) (width : Nat)
    (inside : start+width ≤ bytes.length) :
    Store.decodeBytes (vectorStoreBytes bytes start value 0 width) =
      (Store.decodeBytes bytes).setSlice! start (SpecExt.Builtins.integerBytes width value.val) := by
  rw [vector_store_bytes_set_slice bytes start value width inside]
  unfold Store.decodeBytes
  rw [List.map_setSlice!]
  rw [show (vectorStorePayload value width).map (fun b => byte.mk_byte b.val) =
    SpecExt.Builtins.integerBytes width value.val from vector_store_payload_source value width]
end Itasca.Runtime.Interp.Simd

end

/-! ## LaneStoreSource -/

section

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

end

/-! ## Splat -/

section

/-!
Opcodes and shifts of vector splat loads.

Main declarations: `memorySplatOpcode` and `memorySplatShift`. A direct consumer is `Interp.Simd.Memory.SplatSource`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

def memorySplatOpcode : Jnn → U32
  | .I8 => 7#u32 | .I16 => 8#u32 | .I32 => 9#u32 | .I64 => 10#u32

def memorySplatShift : Jnn → U32
  | .I8 => 0#u32 | .I16 => 1#u32 | .I32 => 2#u32 | .I64 => 3#u32

theorem memory_splat_unfold (ty : Jnn) (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op (memorySplatOpcode ty) offset lane address value memory = (do
      let size ← 1#usize <<< memorySplatShift ty
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset size (Slice.len memory)
      match result with
      | .Err error => .ok (.Err error,memory)
      | .Ok start =>
        let word ← runtime.interp.simd.read memory start size
        let answer ← runtime.interp.simd.splat (UScalar.cast .U64 word) (shiftWidth ty)
        .ok (.Ok answer,memory)) := by
  cases ty
  all_goals dsimp only [memorySplatOpcode,memorySplatShift,shiftWidth]
  all_goals unfold runtime.interp.simd.memory_op
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals congr 1
  all_goals try (with_unfolding_all rfl)
  all_goals funext size
  all_goals try simp only []
  all_goals congr 1
  all_goals try (with_unfolding_all rfl)
  all_goals funext result;cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,core.convert.FromSame.from,lift,bind_ok]
  all_goals congr 1
  all_goals try (with_unfolding_all rfl)
  all_goals funext word
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals with_unfolding_all rfl
end Itasca.Runtime.Interp.Simd
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem memory_splat_effect (ty : Jnn) (offset lane : U32) (address value : U128) (bytes : Slice U8) :
    runtime.interp.simd.memory_op (memorySplatOpcode ty) offset lane address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
        ∃ result, out = (.Ok result,bytes) ∧ uN.mk_uN result.val =
          inv_lanes_ (Spec.Simd.shapeOf (lanetype_Jnn ty))
            (List.replicate (128/lsize (lanetype_Jnn ty))
              (SpecExt.Builtins.laneOfBits (lanetype_Jnn ty)
                ((UScalar.cast .U64 (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val)
                  0#u128 0 (memoryLaneBytes ty).val)).bv.setWidth (lsize (lanetype_Jnn ty))).toNat))
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ⦄ := by
  rw [memory_splat_unfold]
  have shiftBound : (memorySplatShift ty).val ≤ 3 := by cases ty <;> decide
  have shiftFits : (memorySplatShift ty).val < System.Platform.numBits := by
    have := System.Platform.le_numBits
    omega
  step as ⟨size,sizeEq,sizeBits⟩
  have shifted : (1 : Nat) <<< (memorySplatShift ty).val = (memoryLaneBytes ty).val := by
    cases ty <;> simp [memorySplatShift,memoryLaneBytes]
  have sizeVal : size.val = (memoryLaneBytes ty).val := by
    rw [sizeEq,shifted]
    apply Nat.mod_eq_of_lt
    have small := memory_lane_bytes_small ty
    scalar_tac
  step with memory_range bytes (UScalar.cast .U32 address) offset size
    (by rw [sizeVal];exact memory_lane_bytes_small ty) as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · simp only [MemoryAddressEffect,Slice.len_val,sizeVal,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    unfold runtime.interp.simd.read
    step with read_loop_effect bytes size start 0#u128 0#usize
      (by rw [sizeVal];exact memory_lane_bytes_small ty) (by omega) (by simp) as ⟨word,wordEq⟩
    step with splat_packed (lanetype_Jnn ty) (UScalar.cast .U64 word) (shiftWidth ty) (shift_width_val ty)
      as ⟨answer,packed⟩
    simp only [WP.spec_ok,if_pos fits]
    refine ⟨answer,rfl,?_⟩
    simpa only [wordEq,startEq,sizeVal,Nat.sub_zero,Spec.Simd.shapeOf,U64.bv] using packed
  · simp only [MemoryAddressEffect,Slice.len_val,sizeVal,fits,if_false] at effect
    simp only [effect,WP.spec_ok,if_neg fits]
end Itasca.Runtime.Interp.Simd

end

/-! ## SplatSource -/

section

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
    simpa only [memoryEq,offsetEq,Store.decodeBytes,List.length_map,←memory_lane_bytes_val] using Nat.lt_of_not_ge fits
end Itasca.Runtime.Interp.Simd

end

/-! ## StoreSource -/

section

/-!
Source reduction for full-vector stores.

Main declarations: `full_store_source`. A direct consumer is `Interp.Simd.Memory.Relation`.
-/

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
    rw [byteEffect,vector_store_bytes_source bytes.val ((UScalar.cast .U32 address).val+offset.val) value (16) fits]
    rfl
  · rw [if_neg fits] at source effect ⊢
    exact ⟨effect,source⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## ZeroSource -/

section

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

end

/-! ## Relation -/

section

/-!
Exact buffer changes permitted by a vector memory instruction. The write constructor retains both its bounded payload and the corresponding source-store update.

Main declarations: `MemoryBufferChange` and `memorySourceInput`. A direct consumer is `Interp.Simd.Memory.ChangeDecode`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

/-- Exact buffer changes permitted by a vector memory instruction. The write constructor retains
    both its bounded payload and the corresponding source-store update. -/
inductive MemoryBufferChange (s : store) (f : frame) (before : Slice U8) : Slice U8 → store → Prop
  | unchanged : MemoryBufferChange s f before before s
  | write (start : Nat) (payload : List byte) (after : Slice U8)
      (inside : start + payload.length ≤ before.length)
      (payloadWf : Forall wf_byte payload)
      (written : Store.decodeBytes after.val = (Store.decodeBytes before.val).setSlice! start payload) :
      MemoryBufferChange s f before after (Spec.memoryPayloadWrite s f start payload)

theorem MemoryBufferChange.length {s : store} {f : frame} {before after : Slice U8} {sourceAfter : store}
    (change : MemoryBufferChange s f before after sourceAfter) : after.length = before.length := by
  cases change with
  | unchanged => rfl
  | write start payload after inside payloadWf written =>
    simpa only [Store.decodeBytes,List.length_map,List.length_setSlice!,Slice.length] using congrArg List.length written

def memorySourceInput (op : MemoryOperation) (argument : memarg) (laneIndex : Nat)
    (x y z : BitVec 128) : List admininstr :=
  (Spec.Simd.operandValues op.inputs x y z).map admininstr_val ++
    [admininstr_instr (op.instruction argument (.mk_uN laneIndex))]

def MemorySourceEffect (op : MemoryOperation) (argument : memarg) (laneIndex : Nat)
    (x y z : BitVec 128) (s : store) (f : frame) (before : Slice U8)
    (status : core.result.Result U128 runtime.ExecError) (after : Slice U8) : Prop :=
  match status with
  | .Ok value => ∃ sourceAfter, MemoryBufferChange s f before after sourceAfter ∧
      StepH ⟨⟨s,f⟩,memorySourceInput op argument laneIndex x y z⟩ []
        ⟨⟨sourceAfter,f⟩,(Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩
  | .Err error => error = .Trap .MemoryOutOfBounds ∧ after = before ∧
      StepH ⟨⟨s,f⟩,memorySourceInput op argument laneIndex x y z⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩

def MemoryOperationSound (opcode : U32) : Prop :=
  ∀ op, memoryMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (x y z : U128) (bytes : Slice U8) (s : store) (f : frame) (argument : memarg),
    wf_store s → wf_frame f → wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN laneIndex.val))) →
    proj_uN_0 argument.OFFSET = offset.val →
    (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Store.decodeBytes bytes.val →
    0 < f.MODULE.MEMS.length → (op.laneCount ≠ 0 → laneIndex.val < op.laneCount) →
    runtime.interp.simd.memory_op opcode offset laneIndex x y bytes
      ⦃ result => MemorySourceEffect op argument laneIndex.val x.bv y.bv z.bv s f bytes result.1 result.2 ⦄

end Itasca.Runtime.Interp.Simd

end

/-! ## Transition -/

section

/-!
Decoded memory changes and typed SIMD source results.

Main declarations: `MemoryBufferChange.source_change` and `memory_result_types`. A direct consumer is `Interp.Simd.Memory.SourceExecute`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem MemoryBufferChange.source_change {s : store} {f : frame} {before after : Slice U8} {sourceAfter : store}
    (change : MemoryBufferChange s f before after sourceAfter) : SourceMachine.Simd.MemoryChange s f sourceAfter := by
  cases change with
  | unchanged => exact .same
  | write start payload after inside payloadWf written => exact .write start payload payloadWf

theorem memory_result_types (op : MemoryOperation) (value : BitVec 128) :
    (Spec.Simd.operandValues op.outputs value 0 0).map SourceMachine.valueType = op.outputs := by
  cases op <;> rfl

end Itasca.Runtime.Interp.Simd

end

/-! ## ValuesTransition -/

section

/-!
Typed source transitions for returning and trapping SIMD memory effects.

Main declarations: `memory_values_transition` and `memory_values_trap`. A direct consumer is `Interp.Machine.Simd.LaneFrame`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem memory_values_transition (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (op : MemoryOperation) (argument : memarg) (laneIndex : Nat)
    (front values : List val) (value : U128) (sourceAfter : store)
    (split : f.vals = front ++ values) (types : values.map Compiler.valueType = op.inputs)
    (change : SourceMachine.Simd.MemoryChange state.store f.toFrame sourceAfter)
    (effect : StepH ⟨⟨state.store,f.toFrame⟩,
      values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN laneIndex))]⟩ []
      ⟨⟨sourceAfter,f.toFrame⟩,(Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩) :
    SourceMachine.Simd.MemoryTransition state f rest after (op.instruction argument (.mk_uN laneIndex)) op.inputs op.outputs
      (.next ⟨sourceAfter,state.ambient,
        {f with code := after,vals := front ++ Spec.Simd.operandValues op.outputs value.bv 0 0} :: rest,[]⟩) := by
  exact .next front values (Spec.Simd.operandValues op.outputs value.bv 0 0) sourceAfter split (by simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types)
    (memory_result_types op value.bv) change effect

theorem memory_values_trap (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (op : MemoryOperation) (argument : memarg) (laneIndex : Nat) (front values : List val)
    (split : f.vals = front ++ values) (types : values.map Compiler.valueType = op.inputs)
    (effect : StepH ⟨⟨state.store,f.toFrame⟩,
      values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN laneIndex))]⟩ []
      ⟨⟨state.store,f.toFrame⟩,[.TRAP]⟩) :
    SourceMachine.Simd.MemoryTransition state f rest after (op.instruction argument (.mk_uN laneIndex)) op.inputs op.outputs .trap := by
  exact .trap front values split (by simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types) effect
end Itasca.Runtime.Interp.Simd

end

/-! ## ChangeDecode -/

section

/-!
The structured byte effect decodes an actual opaque buffer replacement exactly.

Main declarations: `MemoryBufferChange.decoded`. A direct consumer is `Interp.Simd.Memory.SourceExecute`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt

/-- The structured byte effect decodes an actual opaque buffer replacement exactly. -/
theorem MemoryBufferChange.decoded {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (buffer : M) (sourceAfter : _root_.store)
    (moduleEq : ambient.MODULE = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (found : store.memories.val[address.index.val]? = some object)
    (change : MemoryBufferChange (Store.decodeStore view code store) ambient (view object.buf) (view buffer) sourceAfter) :
    Store.decodeStore view code {store with memories := store.memories.set address.index {object with buf := buffer}} = sourceAfter := by
  generalize bytesEq : view buffer = after at change
  cases change with
  | unchanged => exact memory_unchanged_decodes view code store address object buffer found bytesEq
  | write start payload after inside payloadWf written =>
    exact memory_write_decodes view code store inst ambient address object buffer start payload
      moduleEq mapped found inside (by rw [bytesEq]; exact written)
end Itasca.Runtime.Interp.Simd

end

/-! ## ExecuteEffect -/

section

/-!
Bounded SIMD execution with its exact memory effect.

Main declarations: `execute_simd_memory_effect_bounded`. A direct consumer is `Interp.Simd.Memory.SourceExecute`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem execute_simd_memory_effect_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (op dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32)
    (value : U128)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (bytesAfter : Slice U8) (lengthEq : bytesAfter.length = (view object.buf).length)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (numeric : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) =
        .ok (.Ok value,some bytesAfter)) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => out.1 = .Ok () ∧
        (∃ buffer, out.2.2 = {store with memories := store.memories.set ma.index {object with buf := buffer}} ∧
          view buffer = bytesAfter) ∧ SlotsEffect exec out.2.1
        (simdResultSlots exec.slots.val (base.val+dst.val) wr value) ⦄ := by
  unfold runtime.interp.execute_simd
  step with vec_index_given store.instances instIndex inst found as ⟨actual,eq⟩
  subst actual
  step with vec_index_given inst.module.functions function code compiled as ⟨actual,eq⟩
  subst actual
  try simp only [lift,bind_ok]
  step with vec_index_given code.simd (UScalar.cast .Usize entry) imm (by simpa using immediate) as ⟨actual,eq⟩
  subst actual
  rw [shape,bind_ok]
  try simp only [lift,bind_ok]
  step as ⟨pos,hpos⟩
  step with simd_input_bounded _ pos wa (by intro two; scalar_tac) as ⟨x,hx⟩
  try simp only [lift,bind_ok]
  step as ⟨ypos,hypos⟩
  step with simd_input_bounded _ ypos wb (by intro two; scalar_tac) as ⟨y,hy⟩
  try simp only [lift,bind_ok]
  step as ⟨zpos,hzpos⟩
  step with simd_input_bounded _ zpos wc (by intro two; scalar_tac) as ⟨z,hz⟩
  have hx' : x = simdInput exec.slots.val (base.val+a.val) wa := by simpa [alloc.vec.Vec.deref,hpos] using hx
  have hy' : y = simdInput exec.slots.val (base.val+a.val+wa.val) wb := by simpa [alloc.vec.Vec.deref,hypos,hpos] using hy
  have hz' : z = simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc := by simpa [alloc.vec.Vec.deref,hzpos,hypos,hpos] using hz
  rw [hx',hy',hz']
  have hasMemory : alloc.vec.Vec.len inst.memories > 0#usize := by
    have bound := (List.getElem?_eq_some_iff.mp mapped).1
    scalar_tac
  rw [if_pos hasMemory]
  step with vec_index_given inst.memories 0#usize ma (by simpa using mapped) as ⟨actual,eq⟩
  subst actual
  have memoryBound : ma.index.val < store.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  step as ⟨actual,restore,memRead,memBack⟩
  have actualEq : actual = object := by
    have found := List.getElem?_eq_some_iff.mp issued
    simpa [found.2] using memRead
  rw [actualEq]
  obtain ⟨writeBack,writeCall,writeLaw⟩ := laws.write object.buf
  rw [writeCall,bind_ok]
  have numericSpec : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) ⦃ out => out = (.Ok value,some bytesAfter) ⦄ := by
    rw [numeric]
    simp only [WP.spec_ok]
  step with numericSpec as ⟨status,bytes,statusEq,bytesEq⟩
  subst status bytes

  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have bytesSame := writeLaw bytesAfter lengthEq
  split
  · rename_i positive
    have posNat : 0 < wr.val := by scalar_tac
    try simp only [lift,bind_ok]
    step as ⟨destination,hdestination⟩
    step as ⟨pair,hold,hback⟩
    rcases pair with ⟨old,back⟩
    dsimp only at hold hback ⊢
    try simp only [lift,bind_ok]
    split
    · rename_i two
      step as ⟨shifted,hshifted,shiftBits⟩
      try simp only [lift,bind_ok]
      step as ⟨destination2,hdestination2⟩
      step as ⟨next,hnext⟩
      rw [hback]
      step as ⟨old2,back2,hold2,hback2⟩
      refine ⟨⟨writeBack bytesAfter,?_,bytesSame⟩,?_⟩
      · simp [memBack]
      simp [SlotsEffect,simdResultSlots,posNat,two,hback,hback2,hdestination,hdestination2,hnext]
      congr 1
      exact (UScalar.eq_equiv_bv_eq _ _).mpr (by simpa [UScalar.cast_bv_eq] using congrArg (BitVec.setWidth 64) shiftBits)
    · rename_i other
      with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
      rw [bind_ok]
      with_unfolding_all change Result.ok _ ⦃ _ ⦄
      rw [WP.spec_ok]
      refine ⟨rfl,⟨writeBack bytesAfter,?_,bytesSame⟩,?_⟩
      · simp [memBack]
      simp [SlotsEffect,simdResultSlots,posNat,other,hback,hdestination]
  · rename_i zero
    have zeroNat : ¬0 < wr.val := by scalar_tac
    have notTwo : wr ≠ 2#u32 := by scalar_tac
    simp only [if_neg notTwo,bind_ok,WP.spec_ok]
    refine ⟨rfl,⟨writeBack bytesAfter,?_,bytesSame⟩,?_⟩
    · simp [memBack]
    simp [SlotsEffect,simdResultSlots,zeroNat,notTwo]

end Itasca.Runtime.Interp

end

/-! ## ExecuteError -/

section

/-!
Bounded SIMD execution when the memory operation returns an error.

Main declarations: `execute_simd_memory_error_bounded`. A direct consumer is `Interp.Simd.Memory.SourceExecute`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem execute_simd_memory_error_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (op dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32)
    (error : runtime.ExecError)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (bytesAfter : Slice U8) (lengthEq : bytesAfter.length = (view object.buf).length)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (numeric : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) =
        .ok (.Err error,some bytesAfter)) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => out.1 = .Err error ∧ out.2.1 = exec ∧
        ∃ buffer, out.2.2 = {store with memories := store.memories.set ma.index {object with buf := buffer}} ∧
          view buffer = bytesAfter ⦄ := by
  unfold runtime.interp.execute_simd
  step with vec_index_given store.instances instIndex inst found as ⟨actual,eq⟩
  subst actual
  step with vec_index_given inst.module.functions function code compiled as ⟨actual,eq⟩
  subst actual
  try simp only [lift,bind_ok]
  step with vec_index_given code.simd (UScalar.cast .Usize entry) imm (by simpa using immediate) as ⟨actual,eq⟩
  subst actual
  rw [shape,bind_ok]
  try simp only [lift,bind_ok]
  step as ⟨pos,hpos⟩
  step with simd_input_bounded _ pos wa (by intro two; scalar_tac) as ⟨x,hx⟩
  try simp only [lift,bind_ok]
  step as ⟨ypos,hypos⟩
  step with simd_input_bounded _ ypos wb (by intro two; scalar_tac) as ⟨y,hy⟩
  try simp only [lift,bind_ok]
  step as ⟨zpos,hzpos⟩
  step with simd_input_bounded _ zpos wc (by intro two; scalar_tac) as ⟨z,hz⟩
  have hx' : x = simdInput exec.slots.val (base.val+a.val) wa := by simpa [alloc.vec.Vec.deref,hpos] using hx
  have hy' : y = simdInput exec.slots.val (base.val+a.val+wa.val) wb := by simpa [alloc.vec.Vec.deref,hypos,hpos] using hy
  have hz' : z = simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc := by simpa [alloc.vec.Vec.deref,hzpos,hypos,hpos] using hz
  rw [hx',hy',hz']
  have hasMemory : alloc.vec.Vec.len inst.memories > 0#usize := by
    have bound := (List.getElem?_eq_some_iff.mp mapped).1
    scalar_tac
  rw [if_pos hasMemory]
  step with vec_index_given inst.memories 0#usize ma (by simpa using mapped) as ⟨actual,eq⟩
  subst actual
  have memoryBound : ma.index.val < store.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  step as ⟨actual,restore,memRead,memBack⟩
  have actualEq : actual = object := by
    have found := List.getElem?_eq_some_iff.mp issued
    simpa [found.2] using memRead
  rw [actualEq]
  obtain ⟨writeBack,writeCall,writeLaw⟩ := laws.write object.buf
  rw [writeCall,bind_ok]
  have numericSpec : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) ⦃ out => out = (.Err error,some bytesAfter) ⦄ := by
    rw [numeric]
    simp only [WP.spec_ok]
  step with numericSpec as ⟨status,bytes,statusEq,bytesEq⟩
  subst status bytes

  have bytesSame := writeLaw bytesAfter lengthEq
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame,core.convert.FromSame.from,WP.spec_ok]
  with_unfolding_all change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) ⦃ _ ⦄
  rw [bind_ok,bind_ok]
  with_unfolding_all change Result.ok _ ⦃ _ ⦄
  rw [WP.spec_ok]
  refine ⟨rfl,rfl,writeBack bytesAfter,?_,bytesSame⟩
  simp [memBack]

end Itasca.Runtime.Interp

end
