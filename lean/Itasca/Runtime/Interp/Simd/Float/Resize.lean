import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.Interp.Numeric.Float
import Itasca.Runtime.Interp.Numeric.Float.FloatPromote
import Itasca.Runtime.Interp.Simd.Float.CompareLanes
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes

/-!
Lane promotion and demotion: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Float Resize Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float Platform

def floatResizeWord {F : Type} (floats : runtime.platform.FloatOps F) (kind : FloatResize) (a : U64) : Result U64 := do
  match kind with
  | .demote =>
    let raw ← floats.f32_demote_f64 a
    let value ← runtime.interp.float.quiet32 raw
    Result.ok (UScalar.cast .U64 value)
  | .promote => runtime.interp.float.promote (UScalar.cast .U32 a)

@[step] theorem float_resize_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : FloatResize) (a : U64)
    (bound : a.val < 2^(lsize (lanetype_Fnn kind.input))) :
    floatResizeWord floats kind a ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn kind.output)) result.val ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) a.val) ∧
      result.val < 2^(lsize (lanetype_Fnn kind.output)) ⦄ := by
  cases kind <;> unfold floatResizeWord
  · step with laws.f32_demote_f64 a as ⟨raw,allowed⟩
    step with quiet32_sound raw _ allowed (canonicalClosed_demote 64 32 (by omega) _) as ⟨value,chosen⟩
    refine ⟨?_,?_⟩
    · with_unfolding_all simpa only [U32.cast_U64_val_eq,floatResizeChoices,FloatResize.input,FloatResize.output,lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some] using chosen
    · with_unfolding_all exact value.bv.isLt
  · have castEq : (UScalar.cast .U32 a).val = a.val := by
      with_unfolding_all change a.val % 2^32 = a.val
      exact Nat.mod_eq_of_lt bound
    apply WP.spec_mono (promote_sound (UScalar.cast .U32 a))
    intro value chosen
    refine ⟨?_,?_⟩
    · with_unfolding_all simpa only [castEq,floatResizeChoices,FloatResize.input,FloatResize.output,lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some] using chosen
    · with_unfolding_all exact value.bv.isLt

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Resize Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def floatResizeOpcode : FloatResize → U32 | .demote => 94#u32 | .promote => 95#u32

theorem float_resize_body_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (kind : FloatResize) (x current : U128) (index : U32) :
    runtime.interp.simd.convert_lanes_loop.body floats (floatResizeOpcode kind) x 2#u32 current index =
      (if index < 2#u32 then do
        let a ← runtime.interp.simd.lane x (floatCompareWidth kind.input) index
        let value ← floatResizeWord floats kind a
        let updated ← runtime.interp.simd.put current (floatCompareWidth kind.output) index value
        let next ← index + 1#u32
        Result.ok (ControlFlow.cont (updated,next))
      else do
        Result.ok (ControlFlow.done (core.result.Result.Ok current))) := by
  cases kind
  all_goals unfold runtime.interp.simd.convert_lanes_loop.body floatResizeOpcode
  all_goals with_unfolding_all simp only [floatResizeWord,floatCompareWidth,lift,bind_ok,Std.bind_assoc]
  all_goals with_unfolding_all rfl

theorem float_resize_loop {F : Type} (floats : runtime.platform.FloatOps F)
    (kind : FloatResize) (x initial : U128) (i : U32)
    (R : Nat → BitVec (floatCompareWidth kind.output).val → Prop)
    (wordLaw : ∀ j, j < 2 → ∀ a : U64,
      a.val = (laneBits (floatCompareWidth kind.input).val j x.bv).toNat →
      floatResizeWord floats kind a ⦃ value => R j (value.bv.setWidth (floatCompareWidth kind.output).val) ⦄)
    (position : i.val ≤ 2)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (floatCompareWidth kind.output).val j initial.bv))
    (initializedSuffix : ∀ j, 2 ≤ j → j < 128/(floatCompareWidth kind.output).val →
      laneBits (floatCompareWidth kind.output).val j initial.bv = 0) :
    runtime.interp.simd.convert_lanes_loop floats (floatResizeOpcode kind) x initial i 2#u32
      ⦃ result => ∃ value, result = .Ok value ∧
        (∀ j, j < 2 → R j (laneBits (floatCompareWidth kind.output).val j value.bv)) ∧
        (∀ j, 2 ≤ j → j < 128/(floatCompareWidth kind.output).val →
          laneBits (floatCompareWidth kind.output).val j value.bv = 0) ⦄ := by
  have inputPositive : 0 < (floatCompareWidth kind.input).val := by cases kind <;> decide
  have inputBound : (floatCompareWidth kind.input).val ≤ 64 := by cases kind <;> decide
  have outputPositive : 0 < (floatCompareWidth kind.output).val := by cases kind <;> decide
  have outputBound : (floatCompareWidth kind.output).val ≤ 64 := by cases kind <;> decide
  have outputCount : 2 ≤ 128/(floatCompareWidth kind.output).val := by cases kind <;> decide
  unfold runtime.interp.simd.convert_lanes_loop
  apply loop.spec_decr_nat (fun p => 2-p.2.val)
    (fun p => p.2.val ≤ 2 ∧
      (∀ j, j < p.2.val → R j (laneBits (floatCompareWidth kind.output).val j p.1.bv)) ∧
      (∀ j, 2 ≤ j → j < 128/(floatCompareWidth kind.output).val → laneBits (floatCompareWidth kind.output).val j p.1.bv = 0))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized,zeroed⟩
    dsimp only at indexBound initialized zeroed
    dsimp only
    simp only [float_resize_body_eq]
    split
    · rename_i more
      have less : index.val < 2 := by scalar_tac
      have readRange : (floatCompareWidth kind.input).val*index.val < 128 := by
        cases kind <;> simp only [FloatResize.input,floatCompareWidth] <;> scalar_tac
      step with lane x (floatCompareWidth kind.input) index inputPositive inputBound readRange as ⟨a,aEq⟩
      have aBits : a.val = (laneBits (floatCompareWidth kind.input).val index.val x.bv).toNat := by
        rw [lane_bits_to_nat]; exact aEq
      step with wordLaw index.val less a aBits as ⟨value,allowed⟩
      step with put_lanes current (floatCompareWidth kind.output) index value outputPositive outputBound
        (lane_range _ _ (by omega)) as ⟨updated,same,other⟩
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact allowed
        · rw [other j (lane_range _ _ (by omega)) eq]; exact initialized j (by omega)
      · intro j above bound
        rw [other j (lane_range _ _ bound) (by omega)]
        exact zeroed j above bound
      · omega
    · have finished : index.val = 2 := by scalar_tac
      exact ⟨current,rfl,by simpa [finished] using initialized,zeroed⟩
  · exact ⟨position,initializedPrefix,initializedSuffix⟩

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Resize Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem float_resize_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (kind : FloatResize) (x : U128) :
    runtime.interp.simd.convert_lanes floats (floatResizeOpcode kind) x =
      runtime.interp.simd.convert_lanes_loop floats (floatResizeOpcode kind) x 0#u128 0#u32 2#u32 := by
  cases kind
  all_goals unfold runtime.interp.simd.convert_lanes floatResizeOpcode
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals simp only [bind_ok]

@[step] theorem float_resize_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : FloatResize) (x : U128) :
    runtime.interp.simd.convert_lanes floats (floatResizeOpcode kind) x
      ⦃ result => ∃ value, result = .Ok value ∧
        (∀ j, j < 2 →
          floatOfBits (lsize (lanetype_Fnn kind.output)) (laneBits (lsize (lanetype_Fnn kind.output)) j value.bv).toNat ∈
            floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input))
              (laneBits (lsize (lanetype_Fnn kind.input)) j x.bv).toNat)) ∧
        (∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneBits (lsize (lanetype_Fnn kind.output)) j value.bv = 0) ⦄ := by
  rw [float_resize_dispatch_eq]
  have inputEq := float_compare_width_val kind.input
  have outputEq := float_compare_width_val kind.output
  have spec := float_resize_loop floats kind x 0#u128 0#u32
    (fun j bits => floatOfBits (floatCompareWidth kind.output).val bits.toNat ∈
      floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input))
        (laneBits (lsize (lanetype_Fnn kind.input)) j x.bv).toNat))
    (by
      intro j valid a aEq
      have aBits : a.val = (laneBits (lsize (lanetype_Fnn kind.input)) j x.bv).toNat := by
        cases kind <;> with_unfolding_all exact aEq
      apply WP.spec_mono (float_resize_word floats laws kind a (by rw [aBits]; exact BitVec.isLt _))
      rintro value ⟨chosen,bound⟩
      rw [outputEq]
      have valueNat : (value.bv.setWidth (lsize (lanetype_Fnn kind.output))).toNat = value.val := by
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt bound
      rw [valueNat]
      simpa only [aBits] using chosen)
    (by simp) (by simp) (by intro j above bound; simp [laneBits])
  cases kind <;> with_unfolding_all exact spec

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Float Resize Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem float_resize_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : Spec.Simd.FloatResize) (x : U128) :
    runtime.interp.simd.convert_lanes floats (floatResizeOpcode kind) x ⦃ out =>
      ∃ result, out = .Ok result ∧
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .VCVTOP (Spec.Simd.shapeOf (lanetype_Fnn kind.output)) (Spec.Simd.shapeOf (lanetype_Fnn kind.input))
          (Spec.Simd.floatResizeSource kind)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (float_resize_lanes floats laws kind x)
  rintro out ⟨result,rfl,allowed,zeroed⟩
  exact ⟨result,rfl,Spec.Simd.float_resize_step kind x.bv result.bv allowed zeroed⟩

theorem float_resize_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (kind : Spec.Simd.FloatResize) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatResizeOpcode kind) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.convert_lanes floats (floatResizeOpcode kind) x)
        (fun result => Result.ok (result,memory)) := by
  cases kind
  all_goals unfold runtime.interp.simd.simd floatResizeOpcode
  all_goals with_unfolding_all rfl

@[step] theorem float_resize_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : Spec.Simd.FloatResize)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatResizeOpcode kind) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VCVTOP (Spec.Simd.shapeOf (lanetype_Fnn kind.output)) (Spec.Simd.shapeOf (lanetype_Fnn kind.input))
            (Spec.Simd.floatResizeSource kind)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [float_resize_simd_eq]
  step with float_resize_lanes_sound floats laws kind x as ⟨out,value,eq,source⟩
  subst out
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end
