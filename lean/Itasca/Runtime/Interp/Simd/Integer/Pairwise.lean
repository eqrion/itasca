import Itasca.Runtime.Interp.Simd.Integer.BinaryLoop
import Itasca.Runtime.Interp.Simd.Integer.WidenWords
import Itasca.Runtime.Interp.Simd.Integer.WidenLanes
import Itasca.Runtime.Spec.Simd.Pairwise

/-!
Pairwise extended addition: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Pairwise Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def pairwiseWord (width : U32) (signed : Bool) (a b : U64) : Result U64 := do
  if signed then
    let sa ← runtime.interp.simd.signed a width
    let sb ← runtime.interp.simd.signed b width
    let sum ← sa + sb
    Result.ok (IScalar.hcast .U64 sum)
  else a + b

theorem pairwise_loop (width i : U32) (signed : Bool) (x initial : U128)
    (positive : 0 < width.val) (widthBound : width.val ≤ 32)
    (R : Nat → BitVec (width.val*2) → Prop)
    (wordLaw : ∀ j, j < 64/width.val → ∀ a b : U64,
      a.val = (laneBits width.val (2*j) x.bv).toNat →
      b.val = (laneBits width.val (2*j+1) x.bv).toNat →
      pairwiseWord width signed a b ⦃ value => R j (value.bv.setWidth (width.val*2)) ⦄)
    (position : i.val ≤ 64/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (width.val*2) j initial.bv)) :
    runtime.interp.simd.pairwise_add_lanes_loop x width signed initial i ⦃ result =>
      ∀ j, j < 64/width.val → R j (laneBits (width.val*2) j result.bv) ⦄ := by
  unfold runtime.interp.simd.pairwise_add_lanes_loop
  apply loop.spec_decr_nat (fun p => 64/width.val-p.2.val)
    (fun p => p.2.val ≤ 64/width.val ∧ ∀ j, j < p.2.val → R j (laneBits (width.val*2) j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.pairwise_add_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 64/width.val := by scalar_tac
      have countBound : 64/width.val ≤ 64 := Nat.div_le_self _ _
      have productBound : width.val*(64/width.val) ≤ 64 := Nat.mul_div_le _ _
      have indexProduct : width.val*(index.val+1) ≤ 64 :=
        (Nat.mul_le_mul_left _ less).trans productBound
      have range : width.val*2*index.val+width.val*2 ≤ 128 := by nlinarith
      step as ⟨first,firstEq⟩
      step with lane x width first positive (by omega) (by rw [firstEq]; nlinarith) as ⟨a,aEq⟩
      step as ⟨second,secondEq⟩
      step with lane x width second positive (by omega) (by rw [secondEq,firstEq];nlinarith) as ⟨b,bEq⟩
      have aBits : a.val = (laneBits width.val (2*index.val) x.bv).toNat := by
        rw [lane_bits_to_nat,←firstEq]; exact aEq
      have bBits : b.val = (laneBits width.val (2*index.val+1) x.bv).toNat := by
        rw [lane_bits_to_nat,←firstEq,←secondEq]; exact bEq
      with_unfolding_all change Aeneas.Std.bind (pairwiseWord width signed a b) _ ⦃ _ ⦄
      step with wordLaw index.val less a b aBits bBits as ⟨value,allowed⟩
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

/-! ## Simd Pairwise Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem pairwise_word (width : U32) (signed : Bool) (a b : U64)
    (x y : BitVec width.val) (supported : width.val ∈ [8,16])
    (aBits : a.val = x.toNat) (bBits : b.val = y.toNat) :
    pairwiseWord width signed a b ⦃ result =>
      result.bv.setWidth (width.val*2) = pairwiseBits signed x y ⦄ := by
  have positive : 0 < width.val := by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported;omega
  have bound : width.val ≤ 16 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported;omega
  have aNat : a.val < 65536 := by
    rw [aBits]
    exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) bound)
  have bNat : b.val < 65536 := by
    rw [bBits]
    exact lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) bound)
  have aExact : a.bv = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq;rw [BitVec.toNat_setWidth_of_le (by omega)];exact aBits
  have bExact : b.bv = y.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq;rw [BitVec.toNat_setWidth_of_le (by omega)];exact bBits
  unfold pairwiseWord
  cases signed
  · simp only [Bool.false_eq_true,↓reduceIte]
    step as ⟨value,valueEq⟩
    have valueBits : value.bv = a.bv+b.bv := by
      apply BitVec.eq_of_toNat_eq
      change value.val = (a.val+b.val)%2^64
      rw [←valueEq]
      exact (Nat.mod_eq_of_lt (by scalar_tac)).symm
    refine (congrArg (BitVec.setWidth (width.val*2)) valueBits).trans ?_
    rw [BitVec.setWidth_add _ _ (by omega),aExact,bExact,
      BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_setWidth_of_le _ (by omega)]
    rfl
  · simp only [↓reduceIte]
    step with signed_bits a width positive (by omega) as ⟨sa,saBits⟩
    step with signed_bits b width positive (by omega) as ⟨sb,sbBits⟩
    have saExact : sa.bv = x.signExtend 64 := by
      rw [saBits,aExact,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have sbExact : sb.bv = y.signExtend 64 := by
      rw [sbBits,bExact,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have signedBounds (bits : BitVec width.val) : -32768 ≤ bits.toInt ∧ bits.toInt < 32768 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
      rcases supported with h | h
      all_goals have lo := BitVec.le_toInt bits
      all_goals have hi := BitVec.toInt_lt (x:=bits)
      all_goals simp only [h] at lo hi
      all_goals omega
    have saBound : -32768 ≤ sa.val ∧ sa.val < 32768 := by
      change -32768 ≤ sa.bv.toInt ∧ sa.bv.toInt < 32768
      rw [saExact,BitVec.toInt_signExtend_of_le (by omega)]
      exact signedBounds x
    have sbBound : -32768 ≤ sb.val ∧ sb.val < 32768 := by
      change -32768 ≤ sb.bv.toInt ∧ sb.bv.toInt < 32768
      rw [sbExact,BitVec.toInt_signExtend_of_le (by omega)]
      exact signedBounds y
    step as ⟨value,valueEq⟩
    have valueBits : value.bv = sa.bv+sb.bv := by
      rw [←BitVec.ofInt_toInt (x:=value.bv)]
      change BitVec.ofInt 64 value.val = _
      rw [valueEq,BitVec.ofInt_add]
      simp
    simp only [IScalar.hcast_bv_eq,UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,BitVec.signExtend_eq]
    refine (congrArg (BitVec.setWidth (width.val*2)) valueBits).trans ?_
    rw [BitVec.setWidth_add _ _ (by omega),saExact,sbExact,
      sign_extend_restrict _ _ (by omega),sign_extend_restrict _ _ (by omega)]
    rfl
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Pairwise Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def pairwiseOpcode (ty : PairwiseWidth) (signed : Bool) : U32 :=
  match ty,signed with | .i8,true => 124#u32 | .i8,false => 125#u32 | .i16,true => 126#u32 | .i16,false => 127#u32

theorem pairwise_dispatch_eq (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x =
      (runtime.interp.simd.pairwise_add_lanes_loop x (widenWidth ty.widen) signed 0#u128 0#u32) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.pairwise_add_lanes pairwiseOpcode widenWidth PairwiseWidth.widen
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals with_unfolding_all rfl

@[step] theorem pairwise_lanes (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x ⦃ result =>
      ∀ j, j < ty.widen.count → laneBits (ty.widen.width*2) j result.bv =
        pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv) ⦄ := by
  rw [pairwise_dispatch_eq]
  have widthEq := widen_width_val ty.widen
  have loopLaw := pairwise_loop (widenWidth ty.widen) 0#u32 signed x 0#u128
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = pairwiseBits signed
      (laneBits (widenWidth ty.widen).val (2*j) x.bv) (laneBits (widenWidth ty.widen).val (2*j+1) x.bv))
    (by intro j valid a b aEq bEq; exact pairwise_word _ _ _ _ _ _ (by cases ty <;> decide) aEq bEq)
    (by simp) (by simp)
  apply WP.spec_mono loopLaw
  intro out lanes
  cases ty <;> with_unfolding_all exact lanes
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Pairwise Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem pairwise_packed (ty : PairwiseWidth) (signed : Bool) (x result : U128)
    (lanes : ∀ j, j < ty.widen.count → laneBits (ty.widen.width*2) j result.bv =
      pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv)) :
    uN.mk_uN result.val = pairwiseResult ty signed x.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty.widen.output) ty.widen.count result.bv.toNat
    (fun j => (pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv)).toNat)
    (by intro j valid;rw [←lane_bits_to_nat];cases ty <;> exact congrArg BitVec.toNat (lanes j valid))
  have covers : lsize (lanetype_Jnn ty.widen.output)*ty.widen.count = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold pairwiseResult pairwiseWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty.widen.output) bits = .mk_lane__0 ty.widen.output (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

@[step] theorem pairwise_lanes_sound (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),pairwiseSource ty signed]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (pairwise_lanes ty signed x)
  intro result lanes
  exact pairwise_step ty signed x.bv result.bv (pairwise_packed ty signed x result lanes)

theorem pairwise_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : PairwiseWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (pairwiseOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd pairwiseOpcode
  all_goals with_unfolding_all rfl

@[step] theorem pairwise_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : PairwiseWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (pairwiseOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),pairwiseSource ty signed]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [pairwise_simd_eq]
  step with pairwise_lanes_sound ty signed x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

end
