import Itasca.Runtime.Interp.Simd.Integer.Q15Word
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes
import Itasca.Runtime.Spec.Simd.Q15

/-!
Rounded saturating Q15 multiplication through lane iteration, packed words and source dispatch. The shared scalar Q15 word lemma remains separate for dot products.
-/

/-! ## Simd Q15 Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem q15_loop (x y initial : U128) (i : U32)
    (position : i.val ≤ 8)
    (initializedPrefix : ∀ j, j < i.val → laneBits 16 j initial.bv =
      q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv)) :
    runtime.interp.simd.multiply_lanes_loop 130#u32 x y initial i ⦃ result =>
      ∀ j, j < 8 → laneBits 16 j result.bv = q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv) ⦄ := by
  unfold runtime.interp.simd.multiply_lanes_loop
  apply loop.spec_decr_nat (fun p => 8-p.2.val)
    (fun p => p.2.val ≤ 8 ∧ ∀ j, j < p.2.val → laneBits 16 j p.1.bv =
      q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.multiply_lanes_loop.body
    simp only [↓reduceIte]
    split
    · rename_i more
      have less : index.val < 8 := by scalar_tac
      step with lane x 16#u32 index (by decide) (by decide) (by scalar_tac) as ⟨a,aEq⟩
      have aBits : a.bv.setWidth 16 = laneBits 16 index.val x.bv :=
        lane_word_cast 16 _ _ a (by rw [laneBits_toNat]; exact aEq)
      step with signed a 16#u32 (by decide) (by decide) as ⟨sa,saEq⟩
      step with lane y 16#u32 index (by decide) (by decide) (by scalar_tac) as ⟨b,bEq⟩
      have bBits : b.bv.setWidth 16 = laneBits 16 index.val y.bv :=
        lane_word_cast 16 _ _ b (by rw [laneBits_toNat]; exact bEq)
      step with signed b 16#u32 (by decide) (by decide) as ⟨sb,sbEq⟩
      have aBound : -32768 ≤ sa.val ∧ sa.val < 32768 := by
        rw [saEq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      have bBound : -32768 ≤ sb.val ∧ sb.val < 32768 := by
        rw [sbEq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      rw [←Std.bind_assoc,←Std.bind_assoc,←Std.bind_assoc,←Std.bind_assoc]
      with_unfolding_all change (Aeneas.Std.bind (q15Word sa sb) _) ⦃ _ ⦄
      step with q15_word sa sb aBound bBound as ⟨value,valueEq⟩
      change sa.val = (a.bv.setWidth 16).toInt at saEq
      change sb.val = (b.bv.setWidth 16).toInt at sbEq
      rw [aBits] at saEq
      rw [bBits] at sbEq
      have correct : value.bv.setWidth 16 = q15Bits (laneBits 16 index.val x.bv) (laneBits 16 index.val y.bv) := by
        with_unfolding_all simpa only [q15Bits,saEq,sbEq] using valueEq
      step with put_lanes current 16#u32 index value (by decide) (by decide) (by scalar_tac) as ⟨updated,same,other⟩
      change laneBits 16 index.val updated.bv = value.bv.setWidth 16 at same
      change ∀ j, 16*j+16 ≤ 128 → j ≠ index.val → laneBits 16 j updated.bv = laneBits 16 j current.bv at other
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact correct
        · rw [other j (by omega) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = 8 := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

@[step] theorem q15_lanes (x y : U128) :
    runtime.interp.simd.multiply_lanes 130#u32 x y ⦃ result =>
      ∀ j, j < 8 → laneBits 16 j result.bv = q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv) ⦄ := by
  unfold runtime.interp.simd.multiply_lanes
  apply WP.spec_mono (q15_loop x y 0#u128 0#u32 (by decide) (by simp))
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Q15 Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem q15_packed (x y result : U128)
    (lanes : ∀ j, j < 128/lsize .I16 →
      laneBits (lsize .I16) j result.bv = q15Bits
        (laneBits (lsize .I16) j x.bv) (laneBits (lsize .I16) j y.bv)) :
    uN.mk_uN result.val = q15Result x.bv y.bv := by
  have packed := pack_map_of_lanes .I16 (128/lsize .I16) result.bv.toNat
    (fun j => (q15Bits (laneBits (lsize .I16) j x.bv)
      (laneBits (lsize .I16) j y.bv)).toNat)
    (by intro j valid; rw [←laneBits_toNat,lanes j valid]; rfl)
  rw [shapeOf_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold q15Result q15Words Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits .I16 bits = .mk_lane__0 .I16 (.mk_uN bits) := by rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Q15 Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem q15_lanes_sound (x y : U128)
    :
    runtime.interp.simd.multiply_lanes ((130#u32)) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf .I16) (Spec.Simd.q15Source)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (q15_lanes x y)
  intro result lanes
  exact Spec.Simd.q15_step x.bv y.bv result.bv
    (q15_packed x y result lanes)

theorem q15_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats ((130#u32)) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.multiply_lanes ((130#u32)) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all rfl

@[step] theorem q15_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats ((130#u32)) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf .I16) (Spec.Simd.q15Source)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [q15_simd_eq floats offset laneIndex bits x y z memory]
  step with q15_lanes_sound x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end
