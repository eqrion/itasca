import Itasca.Runtime.Interp.Simd.Integer.UnaryAll
import Itasca.Runtime.Spec.Simd.IntegerSaturating
import Itasca.Runtime.Interp.Simd.Integer.UnaryWords
import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Integer.Q15

/-!
Sections, each formerly its own module: Saturating, PureInteger.
-/

/-! ## Saturating -/

section

/-!
Saturating lane arithmetic: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Integer Saturating Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerSaturatingIndex (kind : IntegerSaturating) : U32 :=
  match kind with | .addS => 15#u32 | .addU => 16#u32 | .subS => 18#u32 | .subU => 19#u32

theorem integer_saturating_word (kind : IntegerSaturating) (width : U32)
    (a b : U64) (sa sb : I64) (supported : width.val ∈ [8,16,32])
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val)
    (saEq : sa.val = (a.bv.setWidth width.val).toInt)
    (sbEq : sb.val = (b.bv.setWidth width.val).toInt) :
    integerBinaryWord (integerSaturatingIndex kind) width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = integerSaturatingBits kind (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  have aCast : (a.val:Int).bmod (2^128) = a.val := Int.bmod_eq_of_le (by scalar_tac) (by scalar_tac)
  have bCast : (b.val:Int).bmod (2^128) = b.val := Int.bmod_eq_of_le (by scalar_tac) (by scalar_tac)
  cases kind
  all_goals unfold integerBinaryWord integerSaturatingIndex
  all_goals with_unfolding_all change (Aeneas.Std.bind _ _) ⦃ _ ⦄
  all_goals step* <;> simp_all [integerSaturatingBits,aCast,bCast,I128.min,I128.max] <;> scalar_tac

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Saturating Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerSaturatingOpcode (ty : Jnn) (kind : IntegerSaturating) : U32 :=
  match ty,kind with
  | .I8,.addS => 111#u32 | .I8,.addU => 112#u32 | .I8,.subS => 114#u32 | .I8,.subU => 115#u32
  | .I16,.addS => 143#u32 | .I16,.addU => 144#u32 | .I16,.subS => 146#u32 | .I16,.subU => 147#u32
  | .I32,.addS => 175#u32 | .I32,.addU => 176#u32 | .I32,.subS => 178#u32 | .I32,.subU => 179#u32
  | .I64,.addS => 207#u32 | .I64,.addU => 208#u32 | .I64,.subS => 210#u32 | .I64,.subU => 211#u32

theorem integer_saturating_opcode_index (ty : Jnn) (kind : IntegerSaturating) :
    (integerSaturatingOpcode ty kind).val%32 = (integerSaturatingIndex kind).val := by
  cases ty <;> cases kind <;> decide

theorem integer_saturating_loop (ty : Jnn) (kind : IntegerSaturating) (x y : U128)
    (supported : integerSaturatingSupported ty kind) :
    runtime.interp.simd.integer_binary_lanes_loop (integerSaturatingOpcode ty kind) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerSaturatingBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integer_compare_width_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (integerSaturatingOpcode ty kind) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = integerSaturatingBits kind (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq saEq sbEq remainderEq
    have exactIndex : remainder = integerSaturatingIndex kind := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (integer_saturating_opcode_index ty kind)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using integer_saturating_word kind (integerCompareWidth ty) a b sa sb
      (by cases ty <;> simp_all [integerSaturatingSupported,integerCompareWidth])
      (by rw [aEq]; exact BitVec.isLt _) (by rw [bEq]; exact BitVec.isLt _) saEq sbEq
  · simp
  · simp

theorem integer_saturating_dispatch_eq (ty : Jnn) (kind : IntegerSaturating) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty kind) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (integerSaturatingOpcode ty kind)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty <;> cases kind
  all_goals unfold runtime.interp.simd.integer_binary_lanes integerSaturatingOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem integer_saturating_lanes (ty : Jnn) (kind : IntegerSaturating) (x y : U128)
    (supported : integerSaturatingSupported ty kind) :
    runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerSaturatingBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [integer_saturating_dispatch_eq]
  apply WP.spec_mono (integer_saturating_loop ty kind x y supported)
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Saturating Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem integer_saturating_packed (ty : Jnn) (kind : IntegerSaturating) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerSaturatingBits kind
        (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv)) :
    uN.mk_uN result.val = integerSaturatingResult ty kind x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (integerSaturatingBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
      (laneBits (lsize (lanetype_Jnn ty)) j y.bv)).toNat)
    (by intro j valid; rw [←lane_bits_to_nat,lanes j valid])
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold integerSaturatingResult saturatingWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty) bits = .mk_lane__0 ty (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Saturating Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem integer_saturating_lanes_sound (ty : Jnn) (op : Spec.Simd.IntegerSaturating) (x y : U128)
    (supported : Spec.Simd.integerSaturatingSupported ty op) :
    runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerSaturatingSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_saturating_lanes ty op x y supported)
  intro result lanes
  exact Spec.Simd.integer_saturating_step ty op x.bv y.bv result.bv supported
    (integer_saturating_packed ty op x y result lanes)

theorem integer_saturating_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : Spec.Simd.IntegerSaturating) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerSaturatingSupported ty op) :
    runtime.interp.simd.simd floats (integerSaturatingOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals simp only [Spec.Simd.integerSaturatingSupported] at supported
  all_goals try contradiction
  all_goals unfold runtime.interp.simd.simd integerSaturatingOpcode
  all_goals with_unfolding_all rfl

@[step] theorem integer_saturating_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : Spec.Simd.IntegerSaturating) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerSaturatingSupported ty op) :
    runtime.interp.simd.simd floats (integerSaturatingOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerSaturatingSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [integer_saturating_simd_eq floats ty op offset laneIndex bits x y z memory supported]
  step with integer_saturating_lanes_sound ty op x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## PureInteger -/

section

/-!
Source correspondence of pure integer opcode entries.

Main declarations: `pure_entry_110` and `pure_entry_213`. A direct consumer is `Interp.Simd.Execution.PureSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_110 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 110#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure110 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I8 .add offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_111 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 111#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure111 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I8 .addS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_112 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 112#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure112 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I8 .addU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_113 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 113#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure113 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I8 .sub offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_114 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 114#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure114 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I8 .subS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_115 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 115#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure115 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I8 .subU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_118 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 118#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure118 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I8 .minS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_119 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 119#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure119 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I8 .minU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_120 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 120#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure120 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I8 .maxS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_121 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 121#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure121 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I8 .maxU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_123 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 123#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure123 = some op at meaning
  cases meaning
  with_unfolding_all exact average_simd_sound floats .I8 offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_130 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 130#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure130 = some op at meaning
  cases meaning
  with_unfolding_all exact q15_simd_sound floats  offset laneIndex bits x y z memory

theorem pure_entry_142 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 142#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure142 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I16 .add offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_143 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 143#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure143 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I16 .addS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_144 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 144#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure144 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I16 .addU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_145 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 145#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure145 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I16 .sub offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_146 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 146#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure146 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I16 .subS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_147 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 147#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure147 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I16 .subU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_149 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 149#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure149 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I16 .mul offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_150 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 150#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure150 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I16 .minS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_151 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 151#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure151 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I16 .minU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_152 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 152#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure152 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I16 .maxS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_153 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 153#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure153 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I16 .maxU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_155 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 155#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure155 = some op at meaning
  cases meaning
  with_unfolding_all exact average_simd_sound floats .I16 offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_174 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 174#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure174 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I32 .add offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_177 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 177#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure177 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I32 .sub offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_181 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 181#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure181 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I32 .mul offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_182 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 182#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure182 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I32 .minS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_183 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 183#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure183 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I32 .minU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_184 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 184#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure184 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I32 .maxS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_185 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 185#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure185 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I32 .maxU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_206 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 206#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure206 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I64 .add offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_209 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 209#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure209 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I64 .sub offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_213 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 213#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure213 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I64 .mul offset laneIndex bits x y z memory (by trivial)

end Itasca.Runtime.Interp.Simd

end
