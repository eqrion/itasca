import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Execution.PureUnary
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Interp.Memory.MemorySize
import Itasca.Runtime.Interp.Simd.Integer.CompareSigned
import SpecExt.Builtins.Examples
import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.Interp.Simd.Lanes.Swizzle
import Itasca.Runtime.Spec.Simd.ExtendLanes

/-!
Sections, each formerly its own module: Execute, Bytes, Range, FullStore, Plain, Dispatch, ExtendLoop, Extend, Lane, LaneEffect, Encoding, LoadSource, LaneBytes, ExtendBytes, ExtendSource.
-/

/-! ## Execute -/

section

/-!
Bounded execution of SIMD operations with memory inputs.

Main declarations: `execute_simd_pure_memory_bounded`. A direct consumer is `Interp.Simd.Execution.ExecuteSource`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem execute_simd_pure_memory_bounded {M F : Type}
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
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (numeric : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) =
        .ok (.Ok value,some (view object.buf))) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => out.1 = .Ok () ∧
        (∃ buffer, out.2.2 = {store with memories := store.memories.set ma.index {object with buf := buffer}} ∧
          view buffer = view object.buf) ∧ SlotsEffect exec out.2.1
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
  step with simd_input_bounded as ⟨x,hx⟩
  try simp only [lift,bind_ok]
  step as ⟨ypos,hypos⟩
  step with simd_input_bounded as ⟨y,hy⟩
  try simp only [lift,bind_ok]
  step as ⟨zpos,hzpos⟩
  step with simd_input_bounded as ⟨z,hz⟩
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
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) (some (view object.buf)) ⦃ out => out = (.Ok value,some (view object.buf)) ⦄ := by
    rw [numeric]
    simp only [WP.spec_ok]
  step with numericSpec as ⟨status,bytes,statusEq,bytesEq⟩
  subst status bytes

  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have bytesSame := writeLaw (view object.buf) rfl
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
      refine ⟨⟨writeBack (view object.buf),?_,bytesSame⟩,?_⟩
      · simp [memBack]
      simp [SlotsEffect,simdResultSlots,posNat,two,hback,hback2,hdestination,hdestination2,hnext]
      congr 1
      exact (UScalar.eq_equiv_bv_eq _ _).mpr (by simpa [UScalar.cast_bv_eq] using congrArg (BitVec.setWidth 64) shiftBits)
    · rename_i other
      with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
      rw [bind_ok]
      with_unfolding_all change Result.ok _ ⦃ _ ⦄
      rw [WP.spec_ok]
      refine ⟨rfl,⟨writeBack (view object.buf),?_,bytesSame⟩,?_⟩
      · simp [memBack]
      simp [SlotsEffect,simdResultSlots,posNat,other,hback,hdestination]
  · rename_i zero
    have zeroNat : ¬0 < wr.val := by scalar_tac
    have notTwo : wr ≠ 2#u32 := by scalar_tac
    simp only [if_neg notTwo,bind_ok,WP.spec_ok]
    refine ⟨rfl,⟨writeBack (view object.buf),?_,bytesSame⟩,?_⟩
    · simp [memBack]
    simp [SlotsEffect,simdResultSlots,zeroNat,notTwo]

end Itasca.Runtime.Interp

end

/-! ## Bytes -/

section

/-!
Byte payloads of vector stores.

Main declarations: `vectorStoreByte` and `vectorStoreBytes`. A direct consumer is `Interp.Simd.Memory.Encoding`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def vectorStoreByte (value : U128) (index : Nat) : U8 :=
  ⟨BitVec.ofNat 8 (value.val >>> (index * 8))⟩

def vectorStoreBytes (bytes : List U8) (start : Nat) (value : U128) (index : Nat) : Nat → List U8
  | 0 => bytes
  | count + 1 => vectorStoreBytes (bytes.set (start + index) (vectorStoreByte value index)) start value (index + 1) count

/-- The complete extracted store loop terminates and writes precisely the
selected little-endian bytes, without changing the buffer length. -/
@[step] theorem write_loop_effect (value : U128) (bytes : Slice U8) (width start index : Usize)
    (small : width.val ≤ 16) (inside : start.val + width.val ≤ bytes.length) (initial : index.val ≤ width.val) :
    runtime.interp.simd.write_loop bytes start width value index ⦃ out =>
      out.val = vectorStoreBytes bytes.val start.val value index.val (width.val - index.val) ⦄ := by
  unfold runtime.interp.simd.write_loop
  apply loop.spec_decr_nat (fun p => width.val - p.2.val)
    (fun p => p.2.val ≤ width.val ∧ p.1.length = bytes.length ∧
      vectorStoreBytes p.1.val start.val value p.2.val (width.val - p.2.val) =
        vectorStoreBytes bytes.val start.val value index.val (width.val - index.val))
  · rintro ⟨current, position⟩ ⟨bound, lengthEq, effect⟩
    dsimp only at bound lengthEq effect
    unfold runtime.interp.simd.write_loop.body
    dsimp only
    split
    · rename_i more
      have positionBound : position.val < width.val := by scalar_tac
      step as ⟨shift, shiftEq⟩
      step as ⟨shifted, shiftedEq, shiftedBits⟩
      step as ⟨destination, destinationEq⟩
      step as ⟨byte, byteCast⟩
      step as ⟨updated, updatedEq⟩
      step as ⟨next, nextEq⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · simpa [updatedEq] using lengthEq
      · have remaining : width.val - position.val = (width.val - next.val) + 1 := by omega
        rw [remaining, vectorStoreBytes] at effect
        have byteEq : UScalar.cast .U8 shifted = vectorStoreByte value position.val := by
          apply UScalar.eq_of_val_eq
          change (UScalar.cast .U8 shifted).val = (value.val >>> (position.val * 8)) % 256
          rw [UScalar.cast_val_eq, shiftedEq, shiftEq]
          rfl
        simpa only [updatedEq, Slice.set_val_eq, destinationEq, nextEq, byteCast, byteEq] using effect
      · omega
    · have finished : position.val = width.val := by scalar_tac
      simpa [finished, vectorStoreBytes] using effect
  · exact ⟨initial, rfl, rfl⟩
/-- Little-endian accumulation in the machine word, with explicit byte position. -/
def vectorLoadByte (value : U128) (byte : U8) (index : Nat) : U128 :=
  value ||| (⟨(UScalar.cast .U128 byte).bv <<< (index * 8)⟩ : U128)

def vectorLoadBytes (bytes : List U8) (start : Nat) (value : U128) (index : Nat) : Nat → U128
  | 0 => value
  | count + 1 => vectorLoadBytes bytes start
      (vectorLoadByte value bytes[start + index]! index) (index + 1) count

/-- The extracted load loop terminates and accumulates exactly the requested
bytes, preserving their little-endian order. -/
@[step] theorem read_loop_effect (bytes : Slice U8) (width start : Usize) (value : U128) (index : Usize)
    (small : width.val ≤ 16) (inside : start.val + width.val ≤ bytes.length) (initial : index.val ≤ width.val) :
    runtime.interp.simd.read_loop bytes start width value index ⦃ out =>
      out = vectorLoadBytes bytes.val start.val value index.val (width.val - index.val) ⦄ := by
  unfold runtime.interp.simd.read_loop
  apply loop.spec_decr_nat (fun p => width.val - p.2.val)
    (fun p => p.2.val ≤ width.val ∧
      vectorLoadBytes bytes.val start.val p.1 p.2.val (width.val - p.2.val) =
        vectorLoadBytes bytes.val start.val value index.val (width.val - index.val))
  · rintro ⟨current, position⟩ ⟨bound, effect⟩
    dsimp only at bound effect
    unfold runtime.interp.simd.read_loop.body
    dsimp only
    split
    · rename_i more
      have positionBound : position.val < width.val := by scalar_tac
      step as ⟨source, sourceEq⟩
      step as ⟨byte, byteEq⟩
      step as ⟨wide, wideEq⟩
      step as ⟨shift, shiftEq⟩
      step as ⟨shifted, shiftedEq, shiftedBits⟩
      step as ⟨updated, updatedEq, updatedBits⟩
      step as ⟨next, nextEq⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · have remaining : width.val - position.val = (width.val - next.val) + 1 := by omega
        rw [remaining, vectorLoadBytes] at effect
        have read : byte = bytes.val[start.val + position.val]! := by
          have bound : start.val + position.val < bytes.val.length := by change start.val + position.val < bytes.length; omega
          rw [getElem!_pos bytes.val _ bound]
          simpa only [sourceEq] using byteEq
        have update : updated = vectorLoadByte current bytes.val[start.val + position.val]! position.val := by
          apply U128.bv_eq_imp_eq
          rw [updatedBits, shiftedBits, wideEq, read, shiftEq]
          rfl
        simpa only [update, nextEq] using effect
      · omega
    · have finished : position.val = width.val := by scalar_tac
      simpa [finished, vectorLoadBytes] using effect
  · exact ⟨initial, rfl⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Range -/

section

/-!
SIMD accesses use the scalar effective-address check against the whole memory.

Main declarations: `memory_range`. A direct consumer is `Interp.Simd.Memory.Extend`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

/-- SIMD accesses use the scalar effective-address check against the whole memory. -/
@[step] theorem memory_range (memory : Slice U8) (address offset : U32) (size : Usize)
    (_small : size.val ≤ 16) :
    runtime.interp.memory.address address offset size (Slice.len memory)
      ⦃ result => MemoryAddressEffect address offset size (Slice.len memory) result ⦄ :=
  memory_address_effect address offset size (Slice.len memory)
end Itasca.Runtime.Interp.Simd

end

/-! ## FullStore -/

section

/-!
Exact memory effects of full-vector stores.

Main declarations: `FullStoreEffect`. A direct consumer is `Interp.Simd.Memory.Dispatch`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem full_store_unfold (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op 11#u32 offset lane address value memory = (do
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset 16#usize (Slice.len memory)
      match result with
      | .Err error => .ok (.Err error,memory)
      | .Ok start =>
        let updated ← runtime.interp.simd.write memory start 16#usize value
        .ok (.Ok 0#u128,updated)) := by
  unfold runtime.interp.simd.memory_op
  simp only [ite_true,lift,bind_ok]
  congr 1
  funext result
  cases result <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from, bind_ok]

def FullStoreEffect (offset : U32) (address value : U128) (memory : Slice U8)
    (out : core.result.Result U128 runtime.ExecError × Slice U8) : Prop :=
  if (UScalar.cast .U32 address).val + offset.val + 16 ≤ memory.length then
    out.1 = .Ok 0#u128 ∧ out.2.val = vectorStoreBytes memory.val
      ((UScalar.cast .U32 address).val + offset.val) value 0 16
  else out = (.Err (.Trap .MemoryOutOfBounds),memory)

@[step] theorem full_store_effect (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op 11#u32 offset lane address value memory
      ⦃ FullStoreEffect offset address value memory ⦄ := by
  rw [full_store_unfold]
  step with memory_range memory (UScalar.cast .U32 address) offset 16#usize (by decide) as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (16#usize).val ≤ memory.length
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    unfold runtime.interp.simd.write
    step with write_loop_effect value memory 16#usize start 0#usize (by decide)
      (by omega) (by simp) as ⟨updated,updatedEq⟩
    simpa [FullStoreEffect,fits,updatedEq,startEq]
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_false] at effect
    have outside : ¬ (UScalar.cast .U32 address).val + offset.val + 16 ≤ memory.length := by simpa using fits
    simp only [effect,WP.spec_ok,FullStoreEffect,if_neg outside]
end Itasca.Runtime.Interp.Simd

end

/-! ## Plain -/

section

/-!
Plain vector-load descriptors and their opcodes.

Main declarations: `PlainLoad` and `PlainLoad.opcode`. A direct consumer is `Interp.Simd.Memory.Dispatch`.
-/

set_option maxHeartbeats 2000000
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

inductive PlainLoad where
  | full | zero32 | zero64

def PlainLoad.opcode : PlainLoad → U32
  | .full => 0#u32 | .zero32 => 92#u32 | .zero64 => 93#u32

def PlainLoad.bytes : PlainLoad → Usize
  | .full => 16#usize | .zero32 => 4#usize | .zero64 => 8#usize

theorem PlainLoad.small (op : PlainLoad) : op.bytes.val ≤ 16 := by cases op <;> decide

theorem plain_load_unfold (op : PlainLoad) (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op op.opcode offset lane address value memory = (do
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset op.bytes (Slice.len memory)
      match result with
      | .Err error => .ok (.Err error,memory)
      | .Ok start =>
        let loaded ← runtime.interp.simd.read memory start op.bytes
        .ok (core.result.Result.Ok loaded,memory)) := by
  cases op <;> unfold PlainLoad.opcode PlainLoad.bytes runtime.interp.simd.memory_op
  all_goals simp only [lift, bind_ok]
  all_goals with_unfolding_all change
    (do
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset _ (Slice.len memory)
      let cf ← core.result.Result.Insts.CoreOpsTry.branch result
      match cf with
      | core.ops.control_flow.ControlFlow.Continue start => do
        let loaded ← runtime.interp.simd.read memory start _
        .ok (core.result.Result.Ok loaded,memory)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          U128 (core.convert.FromSame runtime.ExecError) residual
        .ok (error,memory)) = _
  all_goals congr 1; funext result; cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_ok]
  all_goals with_unfolding_all rfl

def PlainLoadEffect (op : PlainLoad) (offset : U32) (address : U128) (memory : Slice U8)
    (out : core.result.Result U128 runtime.ExecError × Slice U8) : Prop :=
  if (UScalar.cast .U32 address).val + offset.val + op.bytes.val ≤ memory.length then
    out = (.Ok (vectorLoadBytes memory.val ((UScalar.cast .U32 address).val + offset.val)
      0#u128 0 op.bytes.val),memory)
  else out = (.Err (.Trap .MemoryOutOfBounds),memory)

@[step] theorem plain_load_effect (op : PlainLoad) (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op op.opcode offset lane address value memory
      ⦃ PlainLoadEffect op offset address memory ⦄ := by
  rw [plain_load_unfold]
  step with memory_range memory (UScalar.cast .U32 address) offset op.bytes op.small as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + op.bytes.val ≤ memory.length
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    unfold runtime.interp.simd.read
    step with read_loop_effect memory op.bytes start 0#u128 0#usize op.small
      (by omega) (by simp) as ⟨word,wordEq⟩
    simpa [PlainLoadEffect,fits,wordEq,startEq]
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_false] at effect
    simp only [effect,WP.spec_ok,PlainLoadEffect,if_neg fits]
end Itasca.Runtime.Interp.Simd

end

/-! ## Dispatch -/

section

/-!
The SIMD dispatcher equation for memory operations.

Main declarations: `memory_simd_eq`. A direct consumer is `Interp.Simd.Memory.Relation`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem memory_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (op offset lane : U32) (bits x y z : U128) (bytes : Slice U8)
    (memoryOp : op.val ≤ 11 ∨ (84 ≤ op.val ∧ op.val ≤ 93)) :
    runtime.interp.simd.simd floats op offset lane bits x y z (some bytes) =
      Aeneas.Std.bind (runtime.interp.simd.memory_op op offset lane x y bytes)
        (fun out => .ok (out.1,some out.2)) := by
  unfold runtime.interp.simd.simd
  split
  · rfl
  · rename_i larger
    have lower : op ≥ 84#u32 := by scalar_tac
    have upper : op ≤ 93#u32 := by scalar_tac
    rw [if_pos lower,if_pos upper]
    rfl

end Itasca.Runtime.Interp.Simd

end

/-! ## ExtendLoop -/

section

/-!
The runtime loop used by widening vector loads.

Main declarations: `memory_extend_loop`. A direct consumer is `Interp.Simd.Memory.Extend`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
theorem memory_extend_loop (op width i : U32) (x initial : U128)
    (positive : 0 < width.val) (widthBound : width.val ≤ 32)
    (R : Nat → BitVec (width.val*2) → Prop)
    (wordLaw : ∀ j, j < 64/width.val → ∀ a : U64,
      a.val = (laneBits width.val j x.bv).toNat →
      (if op.val % 2 = 1 then do
        let v ← runtime.interp.simd.signed a width
        Result.ok (IScalar.hcast .U64 v) else Result.ok a) ⦃ value => R j (value.bv.setWidth (width.val*2)) ⦄)
    (position : i.val ≤ 64/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (width.val*2) j initial.bv)) :
    runtime.interp.simd.memory_op_loop0 op x width initial i ⦃ result =>
      ∀ j, j < 64/width.val → R j (laneBits (width.val*2) j result.bv) ⦄ := by
  unfold runtime.interp.simd.memory_op_loop0
  apply loop.spec_decr_nat (fun p => 64/width.val-p.2.val)
    (fun p => p.2.val ≤ 64/width.val ∧ ∀ j, j < p.2.val → R j (laneBits (width.val*2) j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.memory_op_loop0.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 64/width.val := by scalar_tac
      have countBound : 64/width.val ≤ 64 := Nat.div_le_self _ _
      have productBound : width.val*(64/width.val) ≤ 64 := Nat.mul_div_le _ _
      have indexProduct : width.val*(index.val+1) ≤ 64 :=
        (Nat.mul_le_mul_left _ less).trans productBound
      have range : width.val*2*index.val+width.val*2 ≤ 128 := by nlinarith
      step with lane x width index positive (by omega) (by nlinarith) as ⟨a,aEq⟩
      have aBits : a.val = (laneBits width.val index.val x.bv).toNat := by
        rw [lane_bits_to_nat];exact aEq
      step as ⟨parity,parityEq⟩
      have parityTest : (parity = 1#u32) = (op.val % 2 = 1) := by scalar_tac
      simp only [parityTest]
      step with wordLaw index.val less a aBits as ⟨value,allowed⟩
      step as ⟨wide,wideEq⟩
      step with put_lanes current wide index value (by omega) (by omega) (by rw [wideEq];exact range) as ⟨updated,same,other⟩
      step as ⟨next,nextEq⟩
      refine ⟨by omega,?_,by omega⟩
      intro j bound
      by_cases eq : j=index.val
      · subst j; rw [wideEq] at same; rw [same]; exact allowed
      · have otherRange : wide.val*j+wide.val ≤ 128 := by
          have le : j ≤ index.val := by omega
          have := Nat.mul_le_mul_left (width.val*2) le
          rw [wideEq]; omega
        rw [wideEq] at other
        rw [other j (by simpa only [wideEq] using otherRange) eq]
        exact initialized j (by omega)
    · have finished : index.val=64/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Extend -/

section

/-!
Opcodes and loops of widening vector loads.

Main declarations: `memoryExtendOpcode` and `memoryExtendLoop`. A direct consumer is `Interp.Simd.Memory.ExtendSource`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd
set_option maxHeartbeats 200000

def memoryExtendOpcode (ty : WidenWidth) (signed : Bool) : U32 :=
  match ty,signed with
  | .i8,true => 1#u32 | .i8,false => 2#u32
  | .i16,true => 3#u32 | .i16,false => 4#u32
  | .i32,true => 5#u32 | .i32,false => 6#u32

def memoryExtendLoop (ty : WidenWidth) (signed : Bool) : U128 → Result U128 :=
  match ty,signed with
  | .i8,true => fun v => runtime.interp.simd.memory_op_loop84 1#u32 v 8#u32 0#u128 0#u32
  | .i8,false => fun v => runtime.interp.simd.memory_op_loop91 2#u32 v 8#u32 0#u128 0#u32
  | .i16,true => fun v => runtime.interp.simd.memory_op_loop98 3#u32 v 16#u32 0#u128 0#u32
  | .i16,false => fun v => runtime.interp.simd.memory_op_loop105 4#u32 v 16#u32 0#u128 0#u32
  | .i32,true => fun v => runtime.interp.simd.memory_op_loop112 5#u32 v 32#u32 0#u128 0#u32
  | .i32,false => fun v => runtime.interp.simd.memory_op_loop119 6#u32 v 32#u32 0#u128 0#u32

theorem memory_extend_unfold (ty : WidenWidth) (signed : Bool)
    (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op (memoryExtendOpcode ty signed) offset lane address value memory = (do
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset 8#usize (Slice.len memory)
      match result with
      | .Err error => .ok (.Err error,memory)
      | .Ok start =>
        let loaded ← runtime.interp.simd.read memory start 8#usize
        let answer ← memoryExtendLoop ty signed loaded
        .ok (core.result.Result.Ok answer,memory)) := by
  cases ty <;> cases signed
  all_goals dsimp only [memoryExtendOpcode,memoryExtendLoop]
  all_goals unfold runtime.interp.simd.memory_op
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rw [if_neg (by decide),if_neg (by decide)]
  all_goals simp only [lift,bind_ok]
  all_goals split <;> try contradiction
  all_goals congr 1
  all_goals funext result;cases result <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,core.convert.FromSame.from]
  all_goals try (with_unfolding_all change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) = _;rw [bind_ok,bind_ok])
  all_goals try (with_unfolding_all rfl)
  all_goals congr 1
  all_goals funext loaded
  all_goals split <;> try contradiction
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals with_unfolding_all rfl
theorem memory_extend_loop_eq (ty : WidenWidth) (signed : Bool) (value : U128) :
    memoryExtendLoop ty signed value =
      runtime.interp.simd.memory_op_loop0 (memoryExtendOpcode ty signed) value (widenWidth ty) 0#u128 0#u32 := by
  cases ty <;> cases signed <;> with_unfolding_all rfl

end Itasca.Runtime.Interp.Simd
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem memory_extend_lanes (ty : WidenWidth) (signed : Bool) (value : U128) :
    runtime.interp.simd.memory_op_loop0 (memoryExtendOpcode ty signed) value (widenWidth ty) 0#u128 0#u32
      ⦃ answer => uN.mk_uN answer.val = widenResult ty false false signed value.bv value.bv ⦄ := by
  have parity : ((memoryExtendOpcode ty signed).val % 2 = 1) = (signed = true) := by cases ty <;> cases signed <;> decide
  have loopLaw := memory_extend_loop (memoryExtendOpcode ty signed) (widenWidth ty) 0#u32 value 0#u128
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = extendBits signed ((widenWidth ty).val*2) (laneBits (widenWidth ty).val j value.bv))
    (by
      intro j valid a aEq
      simp only [parity]
      exact widen_input (widenWidth ty) signed a _ (by cases ty <;> decide) (by cases ty <;> decide) aEq)
    (by simp) (by simp)
  apply WP.spec_mono loopLaw
  intro answer lanes
  apply widen_packed ty false false signed value value answer
  intro j valid
  rw [widen_width_val] at lanes
  have selected := lanes j valid
  simpa only [widen_width_val,widenBits,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using selected

@[step] theorem memory_extend_effect (ty : WidenWidth) (signed : Bool)
    (offset lane : U32) (address value : U128) (bytes : Slice U8) :
    runtime.interp.simd.memory_op (memoryExtendOpcode ty signed) offset lane address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val+offset.val+8 ≤ bytes.length then
        ∃ answer, out = (.Ok answer,bytes) ∧ uN.mk_uN answer.val = widenResult ty false false signed
          (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0 8).bv
          (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0 8).bv
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ⦄ := by
  rw [memory_extend_unfold]
  simp only [memory_extend_loop_eq]
  step with memory_range bytes (UScalar.cast .U32 address) offset 8#usize (by decide) as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val+offset.val+8 ≤ bytes.length
  · simp only [MemoryAddressEffect,Slice.len_val,show (8#usize).val=8 by simp,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    unfold runtime.interp.simd.read
    step with read_loop_effect bytes 8#usize start 0#u128 0#usize (by decide) (by scalar_tac) (by simp)
      as ⟨word,wordEq⟩
    step with memory_extend_lanes ty signed word as ⟨answer,packed⟩
    simp only [if_pos fits]
    refine ⟨answer,rfl,?_⟩
    simpa only [wordEq,startEq,show (8#usize).val=8 by simp,show (0#usize).val=0 by simp,Nat.sub_zero] using packed
  · simp only [MemoryAddressEffect,Slice.len_val,show (8#usize).val=8 by simp,fits,if_false] at effect
    simp only [effect,WP.spec_ok,if_neg fits]
end Itasca.Runtime.Interp.Simd

end

/-! ## Lane -/

section

/-!
Opcodes and byte ranges of vector lane-memory operations.

Main declarations: `memoryLaneOpcode` and `memoryLaneBytes`. A direct consumer is `Interp.Simd.Memory.LaneEffect`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

def memoryLaneOpcode (ty : Jnn) (store : Bool) : U32 :=
  match ty,store with
  | .I8,false => 84#u32 | .I16,false => 85#u32 | .I32,false => 86#u32 | .I64,false => 87#u32
  | .I8,true => 88#u32 | .I16,true => 89#u32 | .I32,true => 90#u32 | .I64,true => 91#u32

def memoryLaneBytes : Jnn → Usize
  | .I8 => UScalar.cast .Usize 1#u32 | .I16 => UScalar.cast .Usize 2#u32
  | .I32 => UScalar.cast .Usize 4#u32 | .I64 => UScalar.cast .Usize 8#u32

theorem memory_lane_bytes_small (ty : Jnn) : (memoryLaneBytes ty).val ≤ 16 := by cases ty <;> simp [memoryLaneBytes]

theorem memory_lane_unfold (ty : Jnn) (store : Bool) (offset index : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty store) offset index address value memory = (do
      if index.val ≥ 128/(shiftWidth ty).val then .ok (.Err runtime.ExecError.Internal,memory)
      else
        let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset (memoryLaneBytes ty) (Slice.len memory)
        match result with
        | .Err error => .ok (.Err error,memory)
        | .Ok start =>
          if store then
            let word ← runtime.interp.simd.lane value (shiftWidth ty) index
            let updated ← runtime.interp.simd.write memory start (memoryLaneBytes ty) (UScalar.cast .U128 word)
            .ok (.Ok 0#u128,updated)
          else
            let word ← runtime.interp.simd.read memory start (memoryLaneBytes ty)
            let updated ← runtime.interp.simd.put value (shiftWidth ty) index (UScalar.cast .U64 word)
            .ok (.Ok updated,memory)) := by
  cases ty <;> cases store
  all_goals dsimp only [memoryLaneOpcode,memoryLaneBytes,shiftWidth]
  all_goals unfold runtime.interp.simd.memory_op
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals first
    | with_unfolding_all change (if index.val ≥ 16 then (_ : Result (core.result.Result U128 runtime.ExecError × Slice U8)) else _) = (if index.val ≥ 16 then _ else _)
    | with_unfolding_all change (if index.val ≥ 8 then (_ : Result (core.result.Result U128 runtime.ExecError × Slice U8)) else _) = (if index.val ≥ 8 then _ else _)
    | with_unfolding_all change (if index.val ≥ 4 then (_ : Result (core.result.Result U128 runtime.ExecError × Slice U8)) else _) = (if index.val ≥ 4 then _ else _)
    | with_unfolding_all change (if index.val ≥ 2 then (_ : Result (core.result.Result U128 runtime.ExecError × Slice U8)) else _) = (if index.val ≥ 2 then _ else _)
  all_goals split <;> try rfl
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals try simp only []
  all_goals congr 1
  all_goals try (with_unfolding_all rfl)
  all_goals try (solve | congr 1; scalar_tac)
  all_goals try dsimp only
  all_goals funext result;cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,core.convert.FromSame.from,lift,bind_ok]
  all_goals try (solve | congr 1; scalar_tac)
  all_goals with_unfolding_all rfl
end Itasca.Runtime.Interp.Simd

end

/-! ## LaneEffect -/

section

/-!
Exact effects of vector lane loads and stores.

Main declarations: `LaneLoadEffect` and `LaneStoreEffect`. A direct consumer is `Interp.Simd.Memory.LaneBytes`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def LaneLoadEffect (ty : Jnn) (offset index : U32) (address value : U128) (bytes : Slice U8)
    (out : core.result.Result U128 runtime.ExecError × Slice U8) : Prop :=
  if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
    ∃ result, out = (.Ok result,bytes) ∧ result.bv =
      writeLaneBits (shiftWidth ty).val index.val value.bv
        (UScalar.cast .U64 (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val)
          0#u128 0 (memoryLaneBytes ty).val)).bv
  else out = (.Err (.Trap .MemoryOutOfBounds),bytes)

@[step] theorem memory_lane_load_effect (ty : Jnn) (offset index : U32) (address value : U128) (bytes : Slice U8)
    (valid : index.val < 128/(shiftWidth ty).val) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty false) offset index address value bytes
      ⦃ LaneLoadEffect ty offset index address value bytes ⦄ := by
  rw [memory_lane_unfold,if_neg (by omega : ¬ index.val ≥ 128/(shiftWidth ty).val)]
  step with memory_range bytes (UScalar.cast .U32 address) offset (memoryLaneBytes ty) (memory_lane_bytes_small ty)
    as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    simp only [Bool.false_eq_true,if_false]
    unfold runtime.interp.simd.read
    step with read_loop_effect bytes (memoryLaneBytes ty) start 0#u128 0#usize (memory_lane_bytes_small ty)
      (by omega) (by simp) as ⟨word,wordEq⟩
    step with put value (shiftWidth ty) index (UScalar.cast .U64 word)
      (by cases ty <;> decide) (by cases ty <;> decide)
      (by cases ty <;> simp [shiftWidth] at valid ⊢ <;> omega) as ⟨answer,bits⟩
    simp only [WP.spec_ok,LaneLoadEffect,if_pos fits]
    refine ⟨answer,rfl,?_⟩
    simpa only [wordEq,startEq,writeLaneBits,Nat.sub_zero] using bits
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_false] at effect
    simp only [effect,WP.spec_ok,LaneLoadEffect,if_neg fits]

def LaneStoreEffect (ty : Jnn) (offset index : U32) (address value : U128) (bytes : Slice U8)
    (out : core.result.Result U128 runtime.ExecError × Slice U8) : Prop :=
  if (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length then
    ∃ word : U64, word.bv = (laneBits (shiftWidth ty).val index.val value.bv).setWidth 64 ∧
      out.1 = .Ok 0#u128 ∧ out.2.val = vectorStoreBytes bytes.val
        ((UScalar.cast .U32 address).val + offset.val) (UScalar.cast .U128 word) 0 (memoryLaneBytes ty).val
  else out = (.Err (.Trap .MemoryOutOfBounds),bytes)

@[step] theorem memory_lane_store_effect (ty : Jnn) (offset index : U32) (address value : U128) (bytes : Slice U8)
    (valid : index.val < 128/(shiftWidth ty).val) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty true) offset index address value bytes
      ⦃ LaneStoreEffect ty offset index address value bytes ⦄ := by
  rw [memory_lane_unfold,if_neg (by omega : ¬ index.val ≥ 128/(shiftWidth ty).val)]
  step with memory_range bytes (UScalar.cast .U32 address) offset (memoryLaneBytes ty) (memory_lane_bytes_small ty)
    as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (memoryLaneBytes ty).val ≤ bytes.length
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    simp only [if_true]
    step with lane_bits value (shiftWidth ty) index
      (by cases ty <;> decide) (by cases ty <;> decide)
      (by cases ty <;> simp [shiftWidth] at valid ⊢ <;> omega) as ⟨word,bits⟩
    unfold runtime.interp.simd.write
    step with write_loop_effect (UScalar.cast .U128 word) bytes (memoryLaneBytes ty) start 0#usize
      (memory_lane_bytes_small ty) (by omega) (by simp) as ⟨updated,updatedEq⟩
    simp only [WP.spec_ok,LaneStoreEffect,if_pos fits]
    exact ⟨word,bits,True.intro,by simpa only [startEq,Nat.sub_zero] using updatedEq⟩
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_false] at effect
    simp only [effect,WP.spec_ok,LaneStoreEffect,if_neg fits]
end Itasca.Runtime.Interp.Simd

end

/-! ## Encoding -/

section

/-!
Byte decoding and source values of vector loads.

Main declarations: `vector_load_byte_value` and `vector_load_bytes_source`. A direct consumer is `Interp.Simd.Memory.LoadSource`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

private theorem power_byte (index : Nat) : 2^(index * 8) = 256^index := by
  rw [Nat.mul_comm, Nat.pow_mul]

theorem vector_load_byte_value (value : U128) (byte : U8) (index : Nat)
    (small : index < 16) (lowerBound : value.val < 256^index) :
    (vectorLoadByte value byte index).val = value.val + byte.val * 256^index := by
  have byteBound : byte.val < 256 := by scalar_tac
  have shiftedBound : byte.val * 256^index < 2^128 := by
    interval_cases index <;> norm_num at * <;> omega
  change (value.bv ||| ((UScalar.cast .U128 byte).bv <<< (index * 8))).toNat = _
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, UScalar.bv_toNat, U8.cast_U128_val_eq]
  rw [Nat.shiftLeft_eq, power_byte, Nat.mod_eq_of_lt shiftedBound]
  have separated := Nat.two_pow_add_eq_or_of_lt (i := index * 8) (by simpa only [power_byte] using lowerBound) byte.val
  simpa only [power_byte, Nat.mul_comm, Nat.add_comm, Nat.or_comm] using separated.symm
/-- The byte loop is the specification's little-endian natural-number decoder,
with an explicit already-filled low prefix. -/
theorem vector_load_bytes_value (bytes : List U8) (start : Nat) (value : U128) (index count : Nat)
    (small : index + count ≤ 16) (inside : start + index + count ≤ bytes.length)
    (lowerBound : value.val < 256^index) :
    (vectorLoadBytes bytes start value index count).val = value.val + 256^index *
      SpecExt.Builtins.integerOfBytes (Store.decodeBytes ((bytes.drop (start + index)).take count)) := by
  induction count generalizing value index with
  | zero => simp [vectorLoadBytes, Store.decodeBytes, SpecExt.Builtins.integerOfBytes]
  | succ count ih =>
    have atIndex : start + index < bytes.length := by omega
    have byteBound : bytes[start + index]!.val < 256 := by scalar_tac
    have nextValue := vector_load_byte_value value bytes[start + index]! index (by omega) lowerBound
    have nextBound : (vectorLoadByte value bytes[start + index]! index).val < 256^(index+1) := by
      rw [nextValue,Nat.pow_succ]
      have positive : 0 < 256^index := by positivity
      nlinarith
    rw [vectorLoadBytes, ih _ (index+1) (by omega) (by omega) nextBound, nextValue]
    rw [List.drop_eq_getElem_cons atIndex]
    simp only [List.take_succ_cons, Store.decodeBytes, List.map_cons, SpecExt.Builtins.integerOfBytes]
    rw [getElem!_pos bytes _ atIndex, Nat.pow_succ]
    have positions : start + (index+1) = start + index + 1 := by omega
    rw [positions]
    ring

theorem vector_load_bytes_source (bytes : List U8) (start count : Nat)
    (small : count ≤ 16) (inside : start + count ≤ bytes.length) :
    (vectorLoadBytes bytes start 0#u128 0 count).val =
      SpecExt.Builtins.integerOfBytes (Store.decodeBytes ((bytes.drop start).take count)) := by
  simpa using vector_load_bytes_value bytes start 0#u128 0 count (by simpa using small)
    (by simpa using inside) (by simp)
end Itasca.Runtime.Interp.Simd

end

/-! ## LoadSource -/

section

/-!
Byte well-formedness and source reduction for full-vector loads.

Main declarations: `memory_bytes_wf` and `full_load_source`. A direct consumer is `Interp.Simd.Memory.LaneBytes`.
-/

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
    rw [vector_load_bytes_source _ _ _ (by decide) fits]
    simpa only [inv_vbytes_,inv_ibytes_,Store.decodeBytes,List.map_take,List.map_drop] using source
  · rw [if_neg fits] at source effect
    rw [effect]
    exact ⟨rfl,rfl,source⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## LaneBytes -/

section

/-!
Byte decoding and widths of vector lane loads.

Main declarations: `memory_lane_bytes_val` and `vector_lane_load_bytes`. A direct consumer is `Interp.Simd.Memory.ExtendBytes`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins

theorem memory_lane_bytes_val (ty : Jnn) : (memoryLaneBytes ty).val = lsize (lanetype_Jnn ty)/8 := by
  cases ty <;> simp [memoryLaneBytes,lsize,lanetype_Jnn,size,valtype_numtype,psize]

theorem vector_lane_load_bound (ty : Jnn) (bytes : List U8) (start : Nat)
    (inside : start+(memoryLaneBytes ty).val ≤ bytes.length) :
    (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val).val < 2^lsize (lanetype_Jnn ty) := by
  rw [vector_load_bytes_source _ _ _ (memory_lane_bytes_small ty) inside]
  have valid := memory_bytes_wf ((bytes.drop start).take (memoryLaneBytes ty).val)
  have bounded := Spec.integer_of_bytes_bound _ valid
  have lengthEq : (Store.decodeBytes ((bytes.drop start).take (memoryLaneBytes ty).val)).length = (memoryLaneBytes ty).val := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  rw [lengthEq] at bounded
  have power : 256^(memoryLaneBytes ty).val = 2^lsize (lanetype_Jnn ty) := by
    cases ty <;> simp [memoryLaneBytes,lsize,lanetype_Jnn,size,valtype_numtype,psize]
  rwa [power] at bounded

theorem vector_lane_load_word (ty : Jnn) (bytes : List U8) (start : Nat)
    (inside : start+(memoryLaneBytes ty).val ≤ bytes.length) :
    ((UScalar.cast .U64 (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val)).bv.setWidth
      (lsize (lanetype_Jnn ty))).toNat =
      (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val).val := by
  have bound := vector_lane_load_bound ty bytes start inside
  have width : lsize (lanetype_Jnn ty) ≤ 64 := by cases ty <;> decide
  have bound64 : (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val).val < 2^64 :=
    lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) width)
  simp only [BitVec.toNat_setWidth,UScalar.bv_toNat,UScalar.cast_val_eq]
  change ((vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val).val % 2^64) % 2^lsize (lanetype_Jnn ty) = _
  rw [Nat.mod_eq_of_lt bound64,Nat.mod_eq_of_lt bound]

theorem vector_lane_load_bytes (ty : Jnn) (bytes : List U8) (start : Nat)
    (inside : start+(memoryLaneBytes ty).val ≤ bytes.length) :
    ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN
      ((UScalar.cast .U64 (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val)).bv.setWidth
        (lsize (lanetype_Jnn ty))).toNat) =
      ((Store.decodeBytes bytes).drop start).take (lsize (lanetype_Jnn ty)/8) := by
  rw [vector_lane_load_word _ _ _ inside,vector_load_bytes_source _ _ _ (memory_lane_bytes_small ty) inside]
  have valid := memory_bytes_wf ((bytes.drop start).take (memoryLaneBytes ty).val)
  have exactBytes := Spec.integer_bytes_of_bytes _ valid
  have lengthEq : (Store.decodeBytes ((bytes.drop start).take (memoryLaneBytes ty).val)).length = (memoryLaneBytes ty).val := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  rw [lengthEq,memory_lane_bytes_val] at exactBytes
  simpa only [ibytes_,proj_uN_0,memory_lane_bytes_val,Store.decodeBytes,List.map_take,List.map_drop] using exactBytes
end Itasca.Runtime.Interp.Simd

end

/-! ## ExtendBytes -/

section

/-!
Byte decoding of widening vector loads.

Main declarations: `vector_extend_load_bytes`. A direct consumer is `Interp.Simd.Memory.ExtendSource`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins Itasca.Runtime.Spec.Simd

theorem vector_extend_load_bytes (ty : WidenWidth) (bytes : List U8) (start j : Nat)
    (inside : start+8 ≤ bytes.length) (lane : j < ty.count) :
    ibytes_ ty.width (.mk_uN (laneWord (lanetype_Jnn ty.input)
      (vectorLoadBytes bytes start 0#u128 0 8).bv j).toNat) =
      ((Store.decodeBytes bytes).drop (start+j*(ty.width/8))).take (ty.width/8) := by
  have payload : integerBytes 8 (vectorLoadBytes bytes start 0#u128 0 8).val =
      ((Store.decodeBytes bytes).drop start).take 8 := by
    rw [vector_load_bytes_source _ _ _ (by decide) inside]
    have roundtrip := Spec.integer_bytes_of_bytes (Store.decodeBytes ((bytes.drop start).take 8))
      (memory_bytes_wf _)
    have len : (Store.decodeBytes ((bytes.drop start).take 8)).length = 8 := by
      simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop];omega
    rw [len] at roundtrip
    simpa only [Store.decodeBytes,List.map_take,List.map_drop] using roundtrip
  have fit : j*(ty.width/8)+ty.width/8 ≤ 8 := by
    cases ty <;> norm_num [WidenWidth.width,WidenWidth.input,WidenWidth.count,lsize,lanetype_Jnn,size,valtype_numtype,psize] at * <;> omega
  have chunk := integer_bytes_chunk (ty.width/8) j (vectorLoadBytes bytes start 0#u128 0 8).val fit
  rw [payload] at chunk
  have pow : 256^(ty.width/8) = 2^ty.width := by cases ty <;> decide
  have offsetPow : 256^(j*(ty.width/8)) = 2^(ty.width*j) := by
    rw [Nat.mul_comm j (ty.width/8),Nat.pow_mul,pow,←Nat.pow_mul]
  rw [offsetPow,pow] at chunk
  change integerBytes (ty.width/8) (laneBits ty.width j (vectorLoadBytes bytes start 0#u128 0 8).bv).toNat = _
  rw [lane_bits_to_nat,UScalar.bv_toNat]
  rw [←chunk,List.drop_take,List.take_take,List.drop_drop]
  rw [Nat.min_eq_left (by omega)]
end Itasca.Runtime.Interp.Simd

end

/-! ## ExtendSource -/

section

/-!
Source reduction for widening vector loads.

Main declarations: `extend_load_source`. A direct consumer is `Interp.Simd.Memory.Relation`.
-/

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

end
