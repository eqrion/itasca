import Itasca.Runtime.Interp.Simd.Memory.EncodingAndEffects
import Itasca.Runtime.Spec.Simd.ArithmeticMemoryAndFloat
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Spec.Simd.LaneOperations
import Itasca.Runtime.Compiler.Local.Lowering.Simd.ConstructionChecks
import Itasca.Runtime.SourceMachine.Simd.MemoryTransition
import Itasca.Runtime.Interp.Simd.Relations.InputValues
import Itasca.Runtime.Interp.Simd.Relations.PureResultSlots
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Memory.EncodingAndDispatch
import Itasca.Runtime.Interp.Simd.Execution.PureUnary
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Memory.MemoryEffects

open WebAssembly

/-!
Proofs for Runtime / Interp / Simd / Memory.

This module collects SourceEffectsAndErrors, ValuesExecute.
Each section documents its contracts and consumers.
-/

/-! ## SourceEffectsAndErrors -/

section

open Itasca.Representation

/-!
# Source Effects And Errors

SIMD memory and lane instructions have the specified source effects and error outcomes.
-/

/-! ## LaneSource -/

section

/-!
Source reduction for vector lane loads.

Main declarations: `lane_load_source`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly

theorem lane_load_source (ty : Jnn) (address value : U128) (offset index : U32) (bytes : Slice U8)
    (valid : index.val < 128/(shiftWidth ty).val)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index.val)))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Representation.decodeBytes bytes.val) :
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
    simpa only [memoryEq,offsetEq,Representation.decodeBytes,List.length_map,←memory_lane_bytes_val] using Nat.lt_of_not_ge fits
end Itasca.Interp.Simd

end

/-! ## StoreEncoding -/

section

/-!
Byte encoding of vector-store payloads.

Main declarations: `vectorStorePayload`.
-/

namespace Itasca.Interp.Simd
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
    (WebAssembly.Builtins.integerBytes count value)[index]? = some (.mk_byte ((value / 256^index) % 256)) := by
  induction index generalizing count value with
  | zero => cases count <;> simp_all [WebAssembly.Builtins.integerBytes]
  | succ index ih =>
    cases count with
    | zero => omega
    | succ count =>
      simpa only [WebAssembly.Builtins.integerBytes,List.getElem?_cons_succ,Nat.pow_succ,
        Nat.div_div_eq_div_mul,Nat.mul_comm] using ih count (value/256) (by omega)

theorem vector_store_payload_source (value : U128) (width : Nat) :
    Representation.decodeBytes (vectorStorePayload value width) = WebAssembly.Builtins.integerBytes width value.val := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < width
  · rw [integer_bytes_at width value.val index inside]
    simp only [Representation.decodeBytes,vectorStorePayload,List.getElem?_map]
    simp only [List.getElem?_range inside,Option.map_some]
    congr 2
    change (value.val >>> (index*8)) % 256 = (value.val / 256^index) % 256
    rw [Nat.shiftRight_eq_div_pow]
    congr 2
    rw [Nat.mul_comm, Nat.pow_mul]
  · have outside : width ≤ index := by omega
    rw [List.getElem?_eq_none (by simpa [Representation.decodeBytes,vectorStorePayload] using outside),
      List.getElem?_eq_none (by simpa only [WebAssembly.Builtins.integer_bytes_length] using outside)]

theorem vector_store_bytes_source (bytes : List U8) (start : Nat) (value : U128) (width : Nat)
    (inside : start+width ≤ bytes.length) :
    Representation.decodeBytes (vectorStoreBytes bytes start value 0 width) =
      (Representation.decodeBytes bytes).setSlice! start (WebAssembly.Builtins.integerBytes width value.val) := by
  rw [vector_store_bytes_set_slice bytes start value width inside]
  unfold Representation.decodeBytes
  rw [List.map_setSlice!]
  rw [show (vectorStorePayload value width).map (fun b => byte.mk_byte b.val) =
    WebAssembly.Builtins.integerBytes width value.val from vector_store_payload_source value width]
end Itasca.Interp.Simd

end

/-! ## LaneStoreSource -/

section

/-!
Lane selection and source reduction for vector lane stores.

Main declarations: `memory_lane_selected` and `lane_store_source`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly WebAssembly.Builtins

theorem memory_lane_selected (ty : Jnn) (index : Nat) (before : BitVec 128)
    (valid : index < 128/lsize (lanetype_Jnn ty)) :
    (lanes_ (Spec.Simd.shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]! =
      .mk_lane__0 ty (.mk_uN (laneBits (lsize (lanetype_Jnn ty)) index before).toNat) := by
  simp only [lanes_,Spec.Simd.shapeOf,proj_uN_0,List.getElem!_eq_getElem?_getD,
    unpack_lanes_get_elem?,if_pos valid,Option.getD_some]
  rw [←lane_bits_to_nat]
  cases ty <;> rfl

theorem lane_store_source (ty : Jnn) (address value : U128) (offset index : U32) (bytes : Slice U8)
    (valid : index.val < 128/(shiftWidth ty).val)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index.val)))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Representation.decodeBytes bytes.val)
    (mapped : 0 < f.MODULE.MEMS.length) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty true) offset index address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
        out.1 = .Ok 0#u128 ∧ Representation.decodeBytes out.2.val =
          (Representation.decodeBytes bytes.val).setSlice! ((UScalar.cast .U32 address).val+offset.val)
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
  simp only [memoryEq,offsetEq,Representation.decodeBytes,List.length_map,←memory_lane_bytes_val] at source
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
end Itasca.Interp.Simd

end

/-! ## Splat -/

section

/-!
Opcodes and shifts of vector splat loads.

Main declarations: `memorySplatOpcode` and `memorySplatShift`.
-/

namespace Itasca.Interp.Simd
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
end Itasca.Interp.Simd
namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem memory_splat_effect (ty : Jnn) (offset lane : U32) (address value : U128) (bytes : Slice U8) :
    runtime.interp.simd.memory_op (memorySplatOpcode ty) offset lane address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
        ∃ result, out = (.Ok result,bytes) ∧ uN.mk_uN result.val =
          inv_lanes_ (Spec.Simd.shapeOf (lanetype_Jnn ty))
            (List.replicate (128/lsize (lanetype_Jnn ty))
              (WebAssembly.Builtins.laneOfBits (lanetype_Jnn ty)
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
end Itasca.Interp.Simd

end

/-! ## SplatSource -/

section

/-!
Source reduction for vector splat loads.

Main declarations: `splat_load_source`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly

theorem splat_load_source (ty : Jnn) (address value : U128) (offset index : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Representation.decodeBytes bytes.val) :
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
    simpa only [memoryEq,offsetEq,Representation.decodeBytes,List.length_map,←memory_lane_bytes_val] using Nat.lt_of_not_ge fits
end Itasca.Interp.Simd

end

/-! ## StoreSource -/

section

/-!
Source reduction for full-vector stores.

Main declarations: `full_store_source`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly
theorem full_store_source (address value : U128) (offset lane : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VSTORE .V128 argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Representation.decodeBytes bytes.val)
    (mapped : 0 < f.MODULE.MEMS.length) :
    runtime.interp.simd.memory_op 11#u32 offset lane address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val + offset.val + 16 ≤ bytes.length then
        out.1 = .Ok 0#u128 ∧ Representation.decodeBytes out.2.val =
          (Representation.decodeBytes bytes.val).setSlice! ((UScalar.cast .U32 address).val+offset.val) (vbytes_ .V128 (.mk_uN value.val)) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VCONST .V128 (.mk_uN value.val),.VSTORE .V128 argument]⟩ []
          ⟨⟨Spec.memoryPayloadWrite s f ((UScalar.cast .U32 address).val+offset.val) (vbytes_ .V128 (.mk_uN value.val)),f⟩,[]⟩
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ∧
        StepH ⟨⟨s,f⟩,[Spec.Segment.i32 (UScalar.cast .U32 address).val,.VCONST .V128 (.mk_uN value.val),.VSTORE .V128 argument]⟩ []
          ⟨⟨s,f⟩,[.TRAP]⟩ ⦄ := by
  have source := Spec.Simd.full_store_step s f argument (UScalar.cast .U32 address).val value.bv
    storeWf frameWf (by scalar_tac) operationWf mapped
  simp only [memoryEq,offsetEq,Representation.decodeBytes,List.length_map] at source
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
end Itasca.Interp.Simd

end

/-! ## ZeroSource -/

section

/-!
Source reduction for zero-extending vector loads.

Main declarations: `zero_load_source`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly
theorem zero_load_source (op : PlainLoad) (zero : op ≠ .full) (address value : U128) (offset lane : U32) (bytes : Slice U8)
    (s : store) (f : frame) (argument : memarg)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.ZERO (.mk_sz (op.bytes.val*8)))) argument))
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (memoryEq : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Representation.decodeBytes bytes.val) :
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
  simp only [Spec.Simd.zeroLoadResult,byteCount,memoryEq,offsetEq,Representation.decodeBytes,List.length_map] at source
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
    simpa only [inv_vbytes_,inv_ibytes_,Representation.decodeBytes,List.map_take,List.map_drop] using source
  · rw [if_neg fits] at source effect
    rw [effect]
    exact ⟨rfl,rfl,source⟩
end Itasca.Interp.Simd

end

/-! ## Relation -/

section

/-!
Exact buffer changes permitted by a vector memory instruction. The write constructor retains both its bounded payload and the corresponding source-store update.

Main declarations: `MemoryBufferChange` and `memorySourceInput`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly Itasca.Body.Simd

/-- Exact buffer changes permitted by a vector memory instruction. The write constructor retains
    both its bounded payload and the corresponding source-store update. -/
inductive MemoryBufferChange (s : store) (f : frame) (before : Slice U8) : Slice U8 → store → Prop
  | unchanged : MemoryBufferChange s f before before s
  | write (start : Nat) (payload : List byte) (after : Slice U8)
      (inside : start + payload.length ≤ before.length)
      (payloadWf : Forall wf_byte payload)
      (written : Representation.decodeBytes after.val = (Representation.decodeBytes before.val).setSlice! start payload) :
      MemoryBufferChange s f before after (Spec.memoryPayloadWrite s f start payload)

theorem MemoryBufferChange.length {s : store} {f : frame} {before after : Slice U8} {sourceAfter : store}
    (change : MemoryBufferChange s f before after sourceAfter) : after.length = before.length := by
  cases change with
  | unchanged => rfl
  | write start payload after inside payloadWf written =>
    simpa only [Representation.decodeBytes,List.length_map,List.length_setSlice!,Slice.length] using congrArg List.length written

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
    (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Representation.decodeBytes bytes.val →
    0 < f.MODULE.MEMS.length → (op.laneCount ≠ 0 → laneIndex.val < op.laneCount) →
    runtime.interp.simd.memory_op opcode offset laneIndex x y bytes
      ⦃ result => MemorySourceEffect op argument laneIndex.val x.bv y.bv z.bv s f bytes result.1 result.2 ⦄

end Itasca.Interp.Simd

end

/-! ## Transition -/

section

/-!
Decoded memory changes and typed SIMD source results.

Main declarations: `MemoryBufferChange.source_change` and `memory_result_types`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly Itasca.Body.Simd

theorem MemoryBufferChange.source_change {s : store} {f : frame} {before after : Slice U8} {sourceAfter : store}
    (change : MemoryBufferChange s f before after sourceAfter) : SourceMachine.Simd.MemoryChange s f sourceAfter := by
  cases change with
  | unchanged => exact .same
  | write start payload after inside payloadWf written => exact .write start payload payloadWf

theorem memory_result_types (op : MemoryOperation) (value : BitVec 128) :
    (Spec.Simd.operandValues op.outputs value 0 0).map SourceMachine.valueType = op.outputs := by
  cases op <;> rfl

end Itasca.Interp.Simd

end

/-! ## ValuesTransition -/

section

/-!
Typed source transitions for returning and trapping SIMD memory effects.

Main declarations: `memory_values_transition` and `memory_values_trap`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly Itasca.Body.Simd

theorem memory_values_transition (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (op : MemoryOperation) (argument : memarg) (laneIndex : Nat)
    (front values : List val) (value : U128) (sourceAfter : store)
    (split : f.vals = front ++ values) (types : values.map Representation.valueType = op.inputs)
    (change : SourceMachine.Simd.MemoryChange state.store f.toFrame sourceAfter)
    (effect : StepH ⟨⟨state.store,f.toFrame⟩,
      values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN laneIndex))]⟩ []
      ⟨⟨sourceAfter,f.toFrame⟩,(Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩) :
    SourceMachine.Simd.MemoryTransition state f rest after (op.instruction argument (.mk_uN laneIndex)) op.inputs op.outputs
      (.next ⟨sourceAfter,state.ambient,
        {f with code := after,vals := front ++ Spec.Simd.operandValues op.outputs value.bv 0 0} :: rest,[]⟩) := by
  exact .next front values (Spec.Simd.operandValues op.outputs value.bv 0 0) sourceAfter split (by simpa only [show Representation.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types)
    (memory_result_types op value.bv) change effect

theorem memory_values_trap (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (op : MemoryOperation) (argument : memarg) (laneIndex : Nat) (front values : List val)
    (split : f.vals = front ++ values) (types : values.map Representation.valueType = op.inputs)
    (effect : StepH ⟨⟨state.store,f.toFrame⟩,
      values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN laneIndex))]⟩ []
      ⟨⟨state.store,f.toFrame⟩,[.TRAP]⟩) :
    SourceMachine.Simd.MemoryTransition state f rest after (op.instruction argument (.mk_uN laneIndex)) op.inputs op.outputs .trap := by
  exact .trap front values split (by simpa only [show Representation.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types) effect
end Itasca.Interp.Simd

end

/-! ## ChangeDecode -/

section

/-!
The structured byte effect decodes an actual opaque buffer replacement exactly.

Main declarations: `MemoryBufferChange.decoded`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly

/-- The structured byte effect decodes an actual opaque buffer replacement exactly. -/
theorem MemoryBufferChange.decoded {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (buffer : M) (sourceAfter : WebAssembly.store)
    (moduleEq : ambient.MODULE = Representation.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (found : store.memories.val[address.index.val]? = some object)
    (change : MemoryBufferChange (Representation.decodeStore view code store) ambient (view object.buf) (view buffer) sourceAfter) :
    Representation.decodeStore view code {store with memories := store.memories.set address.index {object with buf := buffer}} = sourceAfter := by
  generalize bytesEq : view buffer = after at change
  cases change with
  | unchanged => exact memory_unchanged_decodes view code store address object buffer found bytesEq
  | write start payload after inside payloadWf written =>
    exact memory_write_decodes view code store inst ambient address object buffer start payload
      moduleEq mapped found inside (by rw [bytesEq]; exact written)
end Itasca.Interp.Simd

end

/-! ## ExecuteEffect -/

section

/-!
Bounded SIMD execution with its exact memory effect.

Main declarations: `execute_simd_memory_effect_bounded`.
-/

namespace Itasca.Interp
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

end Itasca.Interp

end

/-! ## ExecuteError -/

section

/-!
Bounded SIMD execution when the memory operation returns an error.

Main declarations: `execute_simd_memory_error_bounded`.
-/

namespace Itasca.Interp
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

end Itasca.Interp

end

end

/-! ## ValuesExecute -/

section

open Itasca.Representation

/-!
# Values Execute

SIMD memory entries and writes agree with their source value effects. Concrete execution and source correspondence compose through the retained memory representation.
-/

/-! ## Entries -/

section

/-!
Source correspondence of SIMD memory read opcode entries.

Main declarations: `memory_entry_0` and `memory_entry_93`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly Itasca.Body.Simd

theorem memory_entry_0 : MemoryOperationSound 0#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (full_load_source x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_1 : MemoryOperationSound 1#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load8x8S : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i8 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_2 : MemoryOperationSound 2#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load8x8U : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i8 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_3 : MemoryOperationSound 3#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load16x4S : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i16 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_4 : MemoryOperationSound 4#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load16x4U : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i16 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_5 : MemoryOperationSound 5#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load32x2S : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i32 true x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_6 : MemoryOperationSound 6#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load32x2U : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (extend_load_source .i32 false x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_7 : MemoryOperationSound 7#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.splat8 : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I8 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_8 : MemoryOperationSound 8#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.splat16 : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I16 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_9 : MemoryOperationSound 9#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.splat32 : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I32 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_10 : MemoryOperationSound 10#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.splat64 : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (splat_load_source .I64 x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_84 : MemoryOperationSound 84#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load8Lane : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I8 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_85 : MemoryOperationSound 85#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load16Lane : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I16 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_86 : MemoryOperationSound 86#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load32Lane : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I32 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_87 : MemoryOperationSound 87#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load64Lane : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_load_source .I64 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_92 : MemoryOperationSound 92#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load32Zero : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (zero_load_source .zero32 (by intro h; cases h) x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_93 : MemoryOperationSound 93#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.load64Zero : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (zero_load_source .zero64 (by intro h; cases h) x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq)
  rintro ⟨status,after⟩ ⟨same,source⟩
  dsimp only at same
  subst after
  cases status with
  | Ok value =>
    refine ⟨s,MemoryBufferChange.unchanged,?_⟩
    with_unfolding_all exact source
  | Err error =>
    obtain ⟨errorEq,source⟩ := source
    refine ⟨errorEq,rfl,?_⟩
    with_unfolding_all exact source

end Itasca.Interp.Simd

end

/-! ## WriteEntries -/

section

/-!
Source correspondence of SIMD memory write opcode entries.

Main declarations: `memory_entry_11` and `memory_entry_91`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly Itasca.Body.Simd

theorem memory_entry_11 : MemoryOperationSound 11#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.storeFull : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (full_store_source x y offset index bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + 16 ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (vbytes_ .V128 (.mk_uN y.val)) result.2 ?_ ?_ written,?_⟩
    · simpa only [vbytes_,ibytes_,vsize,WebAssembly.Builtins.integer_bytes_length] using fits
    · exact Spec.integer_bytes_wf 16 y.val
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source
theorem memory_entry_88 : MemoryOperationSound 88#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.store8Lane : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_store_source .I8 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + (memoryLaneBytes .I8).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (WebAssembly.Builtins.integerBytes (memoryLaneBytes .I8).val (laneBits (lsize (lanetype_Jnn .I8)) index.val y.bv).toNat) result.2 ?_ ?_ written,?_⟩
    · simpa only [WebAssembly.Builtins.integer_bytes_length] using fits
    · exact Spec.integer_bytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_89 : MemoryOperationSound 89#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.store16Lane : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_store_source .I16 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + (memoryLaneBytes .I16).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (WebAssembly.Builtins.integerBytes (memoryLaneBytes .I16).val (laneBits (lsize (lanetype_Jnn .I16)) index.val y.bv).toNat) result.2 ?_ ?_ written,?_⟩
    · simpa only [WebAssembly.Builtins.integer_bytes_length] using fits
    · exact Spec.integer_bytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_90 : MemoryOperationSound 90#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.store32Lane : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_store_source .I32 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + (memoryLaneBytes .I32).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (WebAssembly.Builtins.integerBytes (memoryLaneBytes .I32).val (laneBits (lsize (lanetype_Jnn .I32)) index.val y.bv).toNat) result.2 ?_ ?_ written,?_⟩
    · simpa only [WebAssembly.Builtins.integer_bytes_length] using fits
    · exact Spec.integer_bytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

theorem memory_entry_91 : MemoryOperationSound 91#u32 := by
  intro op meaning offset index x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  change some (.store64Lane : MemoryOperation) = some op at meaning
  cases meaning
  apply WP.spec_mono (lane_store_source .I64 x y offset index bytes (valid (by decide)) s f argument storeWf frameWf operationWf offsetEq memoryEq mapped)
  intro result effect
  by_cases fits : (UScalar.cast .U32 x).val + offset.val + (memoryLaneBytes .I64).val ≤ bytes.length
  · rw [if_pos fits] at effect
    obtain ⟨status,written,source⟩ := effect
    unfold MemorySourceEffect
    rw [status]
    refine ⟨_,MemoryBufferChange.write ((UScalar.cast .U32 x).val + offset.val)
      (WebAssembly.Builtins.integerBytes (memoryLaneBytes .I64).val (laneBits (lsize (lanetype_Jnn .I64)) index.val y.bv).toNat) result.2 ?_ ?_ written,?_⟩
    · simpa only [WebAssembly.Builtins.integer_bytes_length] using fits
    · exact Spec.integer_bytes_wf _ _
    · with_unfolding_all exact source
  · rw [if_neg fits] at effect
    obtain ⟨returned,source⟩ := effect
    rw [returned]
    refine ⟨rfl,rfl,?_⟩
    with_unfolding_all exact source

end Itasca.Interp.Simd

end

/-! ## Sound -/

section

/-!
Source-correspondence contracts for SIMD memory opcode entries.

Main declarations: `MemoryEntrySound`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std WebAssembly Itasca.Body.Simd

theorem memory_operation_range {opcode : U32} {op : MemoryOperation}
    (meaning : memoryMeaning opcode.val = some op) : opcode.val ≤ 11 ∨ 84 ≤ opcode.val ∧ opcode.val ≤ 93 := by
  unfold memoryMeaning at meaning
  split at meaning <;> first | contradiction | omega

theorem memory_operation_sound (opcode : U32) : MemoryOperationSound opcode := by
  intro op meaning
  rcases memory_operation_range meaning with lower | ⟨lower,upper⟩
  · generalize h : opcode.val = n at lower
    interval_cases n
    · have eq : opcode = 0#u32 := by scalar_tac
      subst opcode
      exact memory_entry_0 op meaning
    · have eq : opcode = 1#u32 := by scalar_tac
      subst opcode
      exact memory_entry_1 op meaning
    · have eq : opcode = 2#u32 := by scalar_tac
      subst opcode
      exact memory_entry_2 op meaning
    · have eq : opcode = 3#u32 := by scalar_tac
      subst opcode
      exact memory_entry_3 op meaning
    · have eq : opcode = 4#u32 := by scalar_tac
      subst opcode
      exact memory_entry_4 op meaning
    · have eq : opcode = 5#u32 := by scalar_tac
      subst opcode
      exact memory_entry_5 op meaning
    · have eq : opcode = 6#u32 := by scalar_tac
      subst opcode
      exact memory_entry_6 op meaning
    · have eq : opcode = 7#u32 := by scalar_tac
      subst opcode
      exact memory_entry_7 op meaning
    · have eq : opcode = 8#u32 := by scalar_tac
      subst opcode
      exact memory_entry_8 op meaning
    · have eq : opcode = 9#u32 := by scalar_tac
      subst opcode
      exact memory_entry_9 op meaning
    · have eq : opcode = 10#u32 := by scalar_tac
      subst opcode
      exact memory_entry_10 op meaning
    · have eq : opcode = 11#u32 := by scalar_tac
      subst opcode
      exact memory_entry_11 op meaning
  · generalize h : opcode.val = n at lower upper
    interval_cases n
    · have eq : opcode = 84#u32 := by scalar_tac
      subst opcode
      exact memory_entry_84 op meaning
    · have eq : opcode = 85#u32 := by scalar_tac
      subst opcode
      exact memory_entry_85 op meaning
    · have eq : opcode = 86#u32 := by scalar_tac
      subst opcode
      exact memory_entry_86 op meaning
    · have eq : opcode = 87#u32 := by scalar_tac
      subst opcode
      exact memory_entry_87 op meaning
    · have eq : opcode = 88#u32 := by scalar_tac
      subst opcode
      exact memory_entry_88 op meaning
    · have eq : opcode = 89#u32 := by scalar_tac
      subst opcode
      exact memory_entry_89 op meaning
    · have eq : opcode = 90#u32 := by scalar_tac
      subst opcode
      exact memory_entry_90 op meaning
    · have eq : opcode = 91#u32 := by scalar_tac
      subst opcode
      exact memory_entry_91 op meaning
    · have eq : opcode = 92#u32 := by scalar_tac
      subst opcode
      exact memory_entry_92 op meaning
    · have eq : opcode = 93#u32 := by scalar_tac
      subst opcode
      exact memory_entry_93 op meaning

def MemoryEntrySound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) : Prop :=
  ∀ op, memoryMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (bits x y z : U128) (bytes : Slice U8) (s : store) (f : frame) (argument : memarg),
    wf_store s → wf_frame f → wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN laneIndex.val))) →
    proj_uN_0 argument.OFFSET = offset.val →
    (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES = Representation.decodeBytes bytes.val →
    0 < f.MODULE.MEMS.length → (op.laneCount ≠ 0 → laneIndex.val < op.laneCount) →
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z (some bytes)
      ⦃ result => ∃ after, result.2 = some after ∧
        MemorySourceEffect op argument laneIndex.val x.bv y.bv z.bv s f bytes result.1 after ⦄

theorem memory_entry_sound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) :
    MemoryEntrySound floats opcode := by
  intro op meaning offset laneIndex bits x y z bytes s f argument storeWf frameWf operationWf offsetEq memoryEq mapped valid
  rw [memory_simd_eq _ _ _ _ _ _ _ _ _ (memory_operation_range meaning)]
  step with memory_operation_sound opcode op meaning offset laneIndex x y z bytes s f argument
    storeWf frameWf operationWf offsetEq memoryEq mapped valid as ⟨result,effect⟩
  exact ⟨result.2,rfl,effect⟩
end Itasca.Interp.Simd

end

/-! ## SourceExecute -/

section

/-!
Execute any decoded vector memory instruction, retaining its exact source step, slot footprint and single-buffer mutation.

Main declarations: `execute_simd_memory_source`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly Itasca.Body.Simd

/-- Execute any decoded vector memory instruction, retaining its exact source
    step, slot footprint and single-buffer mutation. -/
theorem execute_simd_memory_source {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Representation.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32) (op : MemoryOperation)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape opcode = .ok (some (wa,wb,wc,wr)))
    (meaning : memoryMeaning opcode.val = some op)
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma)
    (issued : store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (f : frame) (argument : memarg)
    (moduleEq : f.MODULE = Representation.decodeInstance store inst)
    (storeWf : wf_store (Representation.decodeStore view interpretation store)) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val)
    (valid : op.laneCount ≠ 0 → imm.lane.val < op.laneCount) :
    let x := simdInput exec.slots.val (base.val+a.val) wa
    let y := simdInput exec.slots.val (base.val+a.val+wa.val) wb
    let z := simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode dst a entry
      ⦃ out => MemoryMutation view store out.2.2 ma object ∧
        match out.1 with
        | .Ok () => ∃ value, SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+dst.val) wr value) ∧
            StepH ⟨⟨Representation.decodeStore view interpretation store,f⟩,
              Simd.memorySourceInput op argument imm.lane.val x.bv y.bv z.bv⟩ []
              ⟨⟨Representation.decodeStore view interpretation out.2.2,f⟩,
                (Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩ ∧
            SourceMachine.Simd.MemoryChange (Representation.decodeStore view interpretation store) f (Representation.decodeStore view interpretation out.2.2)
        | .Err error => error = .Trap .MemoryOutOfBounds ∧ out.2.1 = exec ∧
            Representation.decodeStore view interpretation out.2.2 = Representation.decodeStore view interpretation store ∧
            StepH ⟨⟨Representation.decodeStore view interpretation store,f⟩,
              Simd.memorySourceInput op argument imm.lane.val x.bv y.bv z.bv⟩ []
              ⟨⟨Representation.decodeStore view interpretation store,f⟩,[.TRAP]⟩ ⦄ := by
  dsimp only
  let x := simdInput exec.slots.val (base.val+a.val) wa
  let y := simdInput exec.slots.val (base.val+a.val+wa.val) wb
  let z := simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc
  have memoryEq := memory_lookup_decodes view interpretation store inst f ma object moduleEq mapped issued
  have sourceMap : 0 < f.MODULE.MEMS.length := by
    have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq,Representation.decodeInstance] using bound
  obtain ⟨⟨status,bytes⟩,returned,afterBytes,bytesEq,effect⟩ := WP.spec_imp_exists
    (Simd.memory_entry_sound floats opcode op meaning imm.offset imm.lane imm.bits x y z (view object.buf)
      (Representation.decodeStore view interpretation store) f argument storeWf frameWf operationWf offsetEq
      (by rw [memoryEq]; rfl) sourceMap valid)
  dsimp only at bytesEq
  subst bytes
  cases status with
  | Ok value =>
    obtain ⟨sourceAfter,change,source⟩ := effect
    apply WP.spec_mono (execute_simd_memory_effect_bounded memory floats view laws exec store instIndex function base
      opcode dst a entry inst code imm wa wb wc wr value found compiled immediate shape ma object mapped issued
      afterBytes change.length space lastSpace capacity returned)
    rintro out ⟨status,⟨buffer,changed,bytesEq⟩,slots⟩
    have rawChange : Simd.MemoryBufferChange (Representation.decodeStore view interpretation store) f
        (view object.buf) (view buffer) sourceAfter := by rw [bytesEq]; exact change
    refine ⟨⟨buffer,changed,rawChange.length⟩,?_⟩
    rw [status]
    refine ⟨value,slots,?_⟩
    rw [changed,rawChange.decoded view interpretation store inst f ma object buffer sourceAfter moduleEq mapped issued]
    exact ⟨source,change.source_change⟩
  | Err error =>
    obtain ⟨errorEq,bytesEq,source⟩ := effect
    subst afterBytes
    apply WP.spec_mono (execute_simd_memory_error_bounded memory floats view laws exec store instIndex function base
      opcode dst a entry inst code imm wa wb wc wr error found compiled immediate shape ma object mapped issued
      (view object.buf) rfl space lastSpace capacity returned)
    rintro out ⟨status,execEq,buffer,changed,bytesEq⟩
    refine ⟨⟨buffer,changed,by rw [bytesEq]⟩,?_⟩
    rw [status]
    refine ⟨errorEq,execEq,?_,source⟩
    rw [changed]
    exact memory_unchanged_decodes view interpretation store ma object buffer issued bytesEq
end Itasca.Interp

end

/-! ## ValuesExecute -/

section

/-!
Typed value correspondence for SIMD memory execution.

Main declarations: `ValuesAt.simd_memory_result` and `execute_simd_memory_values`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly Itasca.Body.Simd

private theorem memory_inputs_numeric (op : MemoryOperation) (ty : valtype) (member : ty ∈ op.inputs) :
    ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF := by
  cases ty <;> cases op <;> simp_all [MemoryOperation.inputs,MemoryOperation.store,MemoryOperation.laneCount]

private theorem memory_source_shape (opcode : U32) (op : MemoryOperation) (meaning : memoryMeaning opcode.val = some op) :
    runtime.bytecode.simd_shape opcode = .ok (some (Compiler.simdSourceShape op.inputs op.outputs)) := by
  let C : context := {(default : context) with MEMS := [default]}
  exact (Compiler.SimdImmediateMeaning.memory (C := C) opcode ⟨0#u32,0#u32,0#u128⟩ op meaning
    ⟨.mk_uN 0,.mk_uN 0⟩ 0#u8 default rfl rfl (fun _ => rfl)).shape

theorem ValuesAt.simd_memory_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (op : MemoryOperation) (value : U128)
    (capacity : base + Representation.slots (front.map Representation.valueType) +
      (Compiler.simdSourceWidth op.outputs[0]?).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Representation.slots (front.map Representation.valueType))
      (Compiler.simdSourceWidth op.outputs[0]?) value) base
      (front ++ Spec.Simd.operandValues op.outputs value.bv 0 0) := by
  cases writes : op.store with
  | false =>
    have result := represented.simd_numeric_result .V128 value (by decide)
      (by intro impossible;rcases impossible with h | h <;> cases h)
      (by simpa only [MemoryOperation.outputs,writes,Bool.false_eq_true,↓reduceIte,List.getElem?_cons_zero] using capacity)
    simpa only [MemoryOperation.outputs,writes,Bool.false_eq_true,↓reduceIte,List.getElem?_cons_zero,
      Spec.Simd.operandValues,List.zipWith_cons_cons,List.zipWith_nil_left] using result
  | true =>
    simpa [MemoryOperation.outputs,writes,Compiler.simdSourceWidth,simdResultSlots,Spec.Simd.operandValues] using represented

theorem execute_simd_memory_values {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Representation.CodeInterpretation) (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode operand entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (op : MemoryOperation) (front values : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm) (meaning : memoryMeaning opcode.val = some op)
    (ma : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (mapped : inst.memories.val[0]? = some ma) (issued : store.memories.val[ma.index.val]? = some object)
    (position : operand.val = Representation.slots (front.map Representation.valueType))
    (represented : ValuesAt exec.slots.val base.val (front ++ values))
    (wellFormed : Forall wf_val values) (typed : values.map Representation.valueType = op.inputs)
    (space : base.val + operand.val + (Compiler.simdSourceWidth op.inputs[0]?).val +
      (Compiler.simdSourceWidth op.inputs[1]?).val ≤ Usize.max)
    (lastSpace : Compiler.simdSourceWidth op.inputs[2]? = 2#u32 → base.val + operand.val +
      (Compiler.simdSourceWidth op.inputs[0]?).val + (Compiler.simdSourceWidth op.inputs[1]?).val < Usize.max)
    (capacity : base.val + operand.val + (Compiler.simdSourceWidth op.outputs[0]?).val ≤ exec.slots.length)
    (f : frame) (argument : memarg) (moduleEq : f.MODULE = Representation.decodeInstance store inst)
    (storeWf : wf_store (Representation.decodeStore view interpretation store)) (frameWf : wf_frame f)
    (operationWf : wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))))
    (offsetEq : proj_uN_0 argument.OFFSET = imm.offset.val)
    (valid : op.laneCount ≠ 0 → imm.lane.val < op.laneCount) :
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode operand operand entry
      ⦃ out => MemoryMutation view store out.2.2 ma object ∧
        match out.1 with
        | .Ok () => ∃ value, SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+operand.val)
              (Compiler.simdSourceWidth op.outputs[0]?) value) ∧
            ValuesAt out.2.1.slots.val base.val (front ++ Spec.Simd.operandValues op.outputs value.bv 0 0) ∧
            StepH ⟨⟨Representation.decodeStore view interpretation store,f⟩,
              values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))]⟩ []
              ⟨⟨Representation.decodeStore view interpretation out.2.2,f⟩,
                (Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩ ∧
            SourceMachine.Simd.MemoryChange (Representation.decodeStore view interpretation store) f (Representation.decodeStore view interpretation out.2.2)
        | .Err error => error = .Trap .MemoryOutOfBounds ∧ out.2.1 = exec ∧
            Representation.decodeStore view interpretation out.2.2 = Representation.decodeStore view interpretation store ∧
            StepH ⟨⟨Representation.decodeStore view interpretation store,f⟩,
              values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))]⟩ []
              ⟨⟨Representation.decodeStore view interpretation store,f⟩,[.TRAP]⟩ ⦄ := by
  have numeric : ∀ value ∈ values, Representation.valueType value ≠ .FUNCREF ∧ Representation.valueType value ≠ .EXTERNREF := by
    intro value member
    have m : Representation.valueType value ∈ op.inputs := by rw [←typed]; exact List.mem_map_of_mem member
    exact memory_inputs_numeric op _ m
  have arity : values.length ≤ 3 := by
    have length := congrArg List.length typed
    simp only [List.length_map] at length
    have bound : op.inputs.length ≤ 3 := by cases op <;> decide
    omega
  have inputs := represented.operands.simd_operands wellFormed numeric arity
  dsimp only at inputs
  rw [typed,←position] at inputs
  apply WP.spec_mono (execute_simd_memory_source memory floats interpretation view memoryLaws exec store instIndex function base
    opcode operand operand entry inst code imm
    (Compiler.simdSourceWidth op.inputs[0]?) (Compiler.simdSourceWidth op.inputs[1]?)
    (Compiler.simdSourceWidth op.inputs[2]?) (Compiler.simdSourceWidth op.outputs[0]?) op found compiled immediate
    (memory_source_shape opcode op meaning) meaning ma object mapped issued space lastSpace capacity
    f argument moduleEq storeWf frameWf operationWf offsetEq valid)
  rintro out ⟨mutation,effect⟩
  refine ⟨mutation,?_⟩
  cases status : out.1 with
  | Ok unit =>
    cases unit
    rw [status] at effect
    obtain ⟨value,slots,source,change⟩ := effect
    refine ⟨value,slots,?_,?_,change⟩
    · rw [slots.1,position]
      exact represented.locals.simd_memory_result op value (by simpa only [position] using capacity)
    · unfold Simd.memorySourceInput at source
      rw [inputs] at source
      exact source
  | Err error =>
    rw [status] at effect
    obtain ⟨errorEq,execEq,decoded,source⟩ := effect
    refine ⟨errorEq,execEq,decoded,?_⟩
    unfold Simd.memorySourceInput at source
    rw [inputs] at source
    exact source
end Itasca.Interp

end

end
