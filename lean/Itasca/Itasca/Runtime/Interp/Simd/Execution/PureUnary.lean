import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Integer.ShiftsAndComparison
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticAndReductions
import Itasca.Runtime.Interp.Simd.Float.ComparisonAndConversion
import Itasca.Runtime.Interp.Simd.Lanes.SplatSound

open Itasca.Representation

/-!
# Pure Unary

Pure SIMD execution and conversions agree with the source unary operations and lane representations.
-/

/-! ## ExecutePure -/

section

/-!
Result-slot placement and bounded pure SIMD execution.

Main declarations: `simdResultSlots` and `execute_simd_no_memory_bounded`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def simdResultSlots (words : List U64) (position : Nat) (width : U32) (value : U128) : List U64 :=
  let low := if width.val > 0 then words.set position (UScalar.cast .U64 value) else words
  if width = 2#u32 then low.set (position+1) ⟨(value.bv >>> 64).setWidth 64⟩ else low

theorem execute_simd_no_memory_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (op dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32)
    (value : U128)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (empty : inst.memories.val = [])
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (numeric : runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) none =
        .ok (.Ok value,none)) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => out.1 = .Ok () ∧ out.2.2 = store ∧ SlotsEffect exec out.2.1
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
  have noMemory : ¬alloc.vec.Vec.len inst.memories > 0#usize := by scalar_tac
  rw [if_neg noMemory,numeric,bind_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
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
      simp [SlotsEffect,simdResultSlots,posNat,two,hback,hback2,hdestination,hdestination2,hnext]
      congr 1
      exact (UScalar.eq_equiv_bv_eq _ _).mpr (by simpa [UScalar.cast_bv_eq] using congrArg (BitVec.setWidth 64) shiftBits)
    · rename_i other
      simp [SlotsEffect,simdResultSlots,posNat,other,hback,hdestination]
  · rename_i zero
    have zeroNat : ¬0 < wr.val := by scalar_tac
    have notTwo : wr ≠ 2#u32 := by scalar_tac
    simp [notTwo,SlotsEffect,simdResultSlots,zeroNat]

end Itasca.Interp

end

/-! ## PureConversions -/

section

/-!
Source correspondence of pure conversion opcode entries.

Main declarations: `pure_entry_94` and `pure_entry_255`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_94 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 94#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure94 = some op at meaning
  cases meaning
  with_unfolding_all exact float_resize_simd_sound floats laws .demote offset laneIndex bits x y z memory

theorem pure_entry_95 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 95#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure95 = some op at meaning
  cases meaning
  with_unfolding_all exact float_resize_simd_sound floats laws .promote offset laneIndex bits x y z memory

theorem pure_entry_101 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 101#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure101 = some op at meaning
  cases meaning
  with_unfolding_all exact narrow_simd_sound floats .i8 true offset laneIndex bits x y z memory

theorem pure_entry_102 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 102#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure102 = some op at meaning
  cases meaning
  with_unfolding_all exact narrow_simd_sound floats .i8 false offset laneIndex bits x y z memory

theorem pure_entry_124 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 124#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure124 = some op at meaning
  cases meaning
  with_unfolding_all exact pairwise_simd_sound floats .i8 true offset laneIndex bits x y z memory

theorem pure_entry_125 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 125#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure125 = some op at meaning
  cases meaning
  with_unfolding_all exact pairwise_simd_sound floats .i8 false offset laneIndex bits x y z memory

theorem pure_entry_126 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 126#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure126 = some op at meaning
  cases meaning
  with_unfolding_all exact pairwise_simd_sound floats .i16 true offset laneIndex bits x y z memory

theorem pure_entry_127 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 127#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure127 = some op at meaning
  cases meaning
  with_unfolding_all exact pairwise_simd_sound floats .i16 false offset laneIndex bits x y z memory

theorem pure_entry_133 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 133#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure133 = some op at meaning
  cases meaning
  with_unfolding_all exact narrow_simd_sound floats .i16 true offset laneIndex bits x y z memory

theorem pure_entry_134 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 134#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure134 = some op at meaning
  cases meaning
  with_unfolding_all exact narrow_simd_sound floats .i16 false offset laneIndex bits x y z memory

theorem pure_entry_135 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 135#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure135 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 false false true offset laneIndex bits x y z memory

theorem pure_entry_136 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 136#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure136 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 false true true offset laneIndex bits x y z memory

theorem pure_entry_137 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 137#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure137 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 false false false offset laneIndex bits x y z memory

theorem pure_entry_138 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 138#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure138 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 false true false offset laneIndex bits x y z memory

theorem pure_entry_156 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 156#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure156 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 true false true offset laneIndex bits x y z memory

theorem pure_entry_157 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 157#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure157 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 true true true offset laneIndex bits x y z memory

theorem pure_entry_158 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 158#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure158 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 true false false offset laneIndex bits x y z memory

theorem pure_entry_159 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 159#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure159 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 true true false offset laneIndex bits x y z memory

theorem pure_entry_167 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 167#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure167 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 false false true offset laneIndex bits x y z memory

theorem pure_entry_168 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 168#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure168 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 false true true offset laneIndex bits x y z memory

theorem pure_entry_169 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 169#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure169 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 false false false offset laneIndex bits x y z memory

theorem pure_entry_170 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 170#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure170 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 false true false offset laneIndex bits x y z memory

theorem pure_entry_186 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 186#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure186 = some op at meaning
  cases meaning
  with_unfolding_all exact dot_simd_sound floats  offset laneIndex bits x y z memory

theorem pure_entry_188 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 188#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure188 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 true false true offset laneIndex bits x y z memory

theorem pure_entry_189 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 189#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure189 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 true true true offset laneIndex bits x y z memory

theorem pure_entry_190 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 190#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure190 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 true false false offset laneIndex bits x y z memory

theorem pure_entry_191 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 191#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure191 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 true true false offset laneIndex bits x y z memory

theorem pure_entry_199 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 199#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure199 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 false false true offset laneIndex bits x y z memory

theorem pure_entry_200 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 200#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure200 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 false true true offset laneIndex bits x y z memory

theorem pure_entry_201 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 201#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure201 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 false false false offset laneIndex bits x y z memory

theorem pure_entry_202 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 202#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure202 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 false true false offset laneIndex bits x y z memory

theorem pure_entry_220 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 220#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure220 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 true false true offset laneIndex bits x y z memory

theorem pure_entry_221 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 221#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure221 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 true true true offset laneIndex bits x y z memory

theorem pure_entry_222 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 222#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure222 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 true false false offset laneIndex bits x y z memory

theorem pure_entry_223 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 223#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure223 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 true true false offset laneIndex bits x y z memory

theorem pure_entry_248 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 248#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure248 = some op at meaning
  cases meaning
  with_unfolding_all exact trunc_sat_simd_sound floats .F32 true offset laneIndex bits x y z memory

theorem pure_entry_249 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 249#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure249 = some op at meaning
  cases meaning
  with_unfolding_all exact trunc_sat_simd_sound floats .F32 false offset laneIndex bits x y z memory

theorem pure_entry_250 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 250#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure250 = some op at meaning
  cases meaning
  with_unfolding_all exact convert_integer_simd_sound floats laws .F32 true offset laneIndex bits x y z memory

theorem pure_entry_251 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 251#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure251 = some op at meaning
  cases meaning
  with_unfolding_all exact convert_integer_simd_sound floats laws .F32 false offset laneIndex bits x y z memory

theorem pure_entry_252 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 252#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure252 = some op at meaning
  cases meaning
  with_unfolding_all exact trunc_sat_simd_sound floats .F64 true offset laneIndex bits x y z memory

theorem pure_entry_253 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 253#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure253 = some op at meaning
  cases meaning
  with_unfolding_all exact trunc_sat_simd_sound floats .F64 false offset laneIndex bits x y z memory

theorem pure_entry_254 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 254#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure254 = some op at meaning
  cases meaning
  with_unfolding_all exact convert_integer_simd_sound floats laws .F64 true offset laneIndex bits x y z memory

theorem pure_entry_255 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 255#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure255 = some op at meaning
  cases meaning
  with_unfolding_all exact convert_integer_simd_sound floats laws .F64 false offset laneIndex bits x y z memory

end Itasca.Interp.Simd

end

/-! ## PureUnary -/

section

/-!
Source correspondence of pure unary opcode entries.

Main declarations: `pure_entry_15` and `pure_entry_205`.
-/

namespace Itasca.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_15 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 15#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure15 = some op at meaning
  cases meaning
  have h := splat_dispatch_sound floats .I8 offset laneIndex bits x y z memory
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  with_unfolding_all exact h

theorem pure_entry_16 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 16#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure16 = some op at meaning
  cases meaning
  have h := splat_dispatch_sound floats .I16 offset laneIndex bits x y z memory
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  with_unfolding_all exact h

theorem pure_entry_17 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 17#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure17 = some op at meaning
  cases meaning
  have h := splat_dispatch_sound floats .I32 offset laneIndex bits x y z memory
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  with_unfolding_all exact h

theorem pure_entry_18 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 18#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure18 = some op at meaning
  cases meaning
  with_unfolding_all exact splat_dispatch_sound floats .I64 offset laneIndex bits x y z memory

theorem pure_entry_19 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 19#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure19 = some op at meaning
  cases meaning
  have h := splat_dispatch_sound floats .F32 offset laneIndex bits x y z memory
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  with_unfolding_all exact h

theorem pure_entry_20 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 20#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure20 = some op at meaning
  cases meaning
  with_unfolding_all exact splat_dispatch_sound floats .F64 offset laneIndex bits x y z memory

theorem pure_entry_96 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 96#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure96 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I8 .absolute offset laneIndex bits x y z memory

theorem pure_entry_97 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 97#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure97 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I8 .negate offset laneIndex bits x y z memory

theorem pure_entry_98 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 98#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure98 = some op at meaning
  cases meaning
  with_unfolding_all exact popcount_dispatch_sound floats  offset laneIndex bits x y z memory

theorem pure_entry_99 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 99#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure99 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I8 .allTrue) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [all_true_dispatch_eq]
  step with all_true_lanes_sound .I8 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_100 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 100#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure100 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I8 .bitmask) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [bitmask_dispatch_eq]
  step with bitmask_lanes_sound .I8 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_107 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 107#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure107 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I8 .left offset laneIndex bits x y z memory

theorem pure_entry_108 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 108#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure108 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I8 .signedRight offset laneIndex bits x y z memory

theorem pure_entry_109 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 109#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure109 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I8 .unsignedRight offset laneIndex bits x y z memory

theorem pure_entry_128 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 128#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure128 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I16 .absolute offset laneIndex bits x y z memory

theorem pure_entry_129 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 129#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure129 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I16 .negate offset laneIndex bits x y z memory

theorem pure_entry_131 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 131#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure131 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I16 .allTrue) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [all_true_dispatch_eq]
  step with all_true_lanes_sound .I16 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_132 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 132#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure132 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I16 .bitmask) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [bitmask_dispatch_eq]
  step with bitmask_lanes_sound .I16 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_139 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 139#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure139 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I16 .left offset laneIndex bits x y z memory

theorem pure_entry_140 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 140#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure140 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I16 .signedRight offset laneIndex bits x y z memory

theorem pure_entry_141 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 141#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure141 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I16 .unsignedRight offset laneIndex bits x y z memory

theorem pure_entry_160 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 160#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure160 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I32 .absolute offset laneIndex bits x y z memory

theorem pure_entry_161 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 161#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure161 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I32 .negate offset laneIndex bits x y z memory

theorem pure_entry_163 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 163#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure163 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I32 .allTrue) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [all_true_dispatch_eq]
  step with all_true_lanes_sound .I32 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_164 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 164#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure164 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I32 .bitmask) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [bitmask_dispatch_eq]
  step with bitmask_lanes_sound .I32 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_171 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 171#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure171 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I32 .left offset laneIndex bits x y z memory

theorem pure_entry_172 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 172#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure172 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I32 .signedRight offset laneIndex bits x y z memory

theorem pure_entry_173 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 173#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure173 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I32 .unsignedRight offset laneIndex bits x y z memory

theorem pure_entry_192 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 192#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure192 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I64 .absolute offset laneIndex bits x y z memory

theorem pure_entry_193 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 193#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure193 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I64 .negate offset laneIndex bits x y z memory

theorem pure_entry_195 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 195#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure195 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I64 .allTrue) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [all_true_dispatch_eq]
  step with all_true_lanes_sound .I64 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_196 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 196#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure196 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I64 .bitmask) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [bitmask_dispatch_eq]
  step with bitmask_lanes_sound .I64 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_203 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 203#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure203 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I64 .left offset laneIndex bits x y z memory

theorem pure_entry_204 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 204#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure204 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I64 .signedRight offset laneIndex bits x y z memory

theorem pure_entry_205 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 205#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Body.Simd.Operation.pure205 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I64 .unsignedRight offset laneIndex bits x y z memory

end Itasca.Interp.Simd

end
