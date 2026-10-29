import Itasca.Runtime.Interp.Simd.Integer.Saturation
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes
import Itasca.Runtime.Spec.Simd.Narrow

/-!
Narrowing lane arithmetic: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Narrow Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def narrowLane (width : Nat) (signed : Bool) (x y : BitVec 128) (j : Nat) : BitVec width :=
  BitVec.ofInt width (clampLane width signed
    (laneBits (width*2) (j%(64/width)) (if j < 64/width then x else y)).toInt)

theorem narrow_loop (x y initial : U128) (width i : U32) (signedFlag : Bool)
    (supported : width.val ∈ [8,16]) (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv = narrowLane width.val signedFlag x.bv y.bv j) :
    runtime.interp.simd.narrow_lanes_loop x y width signedFlag initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = narrowLane width.val signedFlag x.bv y.bv j ⦄ := by
  have positive : 0 < width.val := by simp_all; omega
  have widthBound : width.val ≤ 64 := by simp_all; omega
  have halfPositive : 0 < 64/width.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
    rcases supported with h | h <;> rw [h] <;> decide
  have wideBound : width.val*2 ≤ 64 := by simp_all; omega
  unfold runtime.interp.simd.narrow_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧ ∀ j, j < p.2.val →
      laneBits width.val j p.1.bv = narrowLane width.val signedFlag x.bv y.bv j)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.narrow_lanes_loop.body
    dsimp only
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      step as ⟨half,halfEq⟩
      have selectEq : (if index < half then Result.ok x else Result.ok y) = Result.ok (if index < half then x else y) := by split <;> rfl
      rw [selectEq,bind_ok]
      step as ⟨wide,wideEq⟩
      step as ⟨laneIndex,laneIndexEq⟩
      have laneBound : wide.val*laneIndex.val < 128 := by
        rw [wideEq,laneIndexEq,halfEq]
        have modBound := Nat.mod_lt index.val halfPositive
        simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
        rcases supported with h | h <;> rw [h] at * <;> omega
      step with lane (if index < half then x else y) wide laneIndex (by scalar_tac) (by scalar_tac) laneBound as ⟨a,aEq⟩
      have aBits := lane_word_cast wide.val laneIndex.val (if index < half then x else y).bv a (by rw [lane_bits_to_nat]; exact aEq)
      step with signed a wide (by scalar_tac) (by scalar_tac) as ⟨sa,saEq⟩
      step as ⟨widened,widenedEq⟩
      step with saturate widened width signedFlag (by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported ⊢; rcases supported with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) as ⟨value,valueEq⟩
      have widenedVal : widened.val = sa.val := by simp [widenedEq]
      have correct : value.bv.setWidth width.val = narrowLane width.val signedFlag x.bv y.bv index.val := by
        rw [valueEq,widenedVal,saEq,aBits]
        with_unfolding_all rw [wideEq]
        simp only [laneIndexEq,UScalar.lt_equiv,halfEq,narrowLane]
        split <;> rfl
      step with put_lanes current width index value positive widthBound (lane_range _ _ less) as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact correct
        · rw [other j (lane_range _ _ (by omega)) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Narrow Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def narrowWidth : NarrowWidth → U32 | .i8 => 8#u32 | .i16 => 16#u32

def narrowOpcode (ty : NarrowWidth) (signed : Bool) : U32 :=
  match ty,signed with
  | .i8,true => 101#u32 | .i8,false => 102#u32
  | .i16,true => 133#u32 | .i16,false => 134#u32

theorem narrow_dispatch_eq (ty : NarrowWidth) (signed : Bool) (x y : U128) :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y =
      (runtime.interp.simd.narrow_lanes_loop x y (narrowWidth ty) signed 0#u128 0#u32) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.narrow_lanes narrowOpcode narrowWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem narrow_lanes (ty : NarrowWidth) (signed : Bool) (x y : U128) :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y ⦃ result =>
      ∀ j, j < 128/ty.width → laneBits ty.width j result.bv = narrowLane ty.width signed x.bv y.bv j ⦄ := by
  rw [narrow_dispatch_eq]
  apply WP.spec_mono (narrow_loop x y 0#u128 (narrowWidth ty) 0#u32 signed (by cases ty <;> decide) (by simp) (by simp))
  intro result lanes
  cases ty <;> with_unfolding_all exact lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Narrow Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem narrow_packed (ty : NarrowWidth) (signed : Bool) (x y result : U128)
    (lanes : ∀ j, j < 128/ty.width → laneBits ty.width j result.bv = narrowLane ty.width signed x.bv y.bv j) :
    uN.mk_uN result.val = narrowResult ty signed x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty.output) (128/ty.width) result.bv.toNat
    (fun j => (narrowLane ty.width signed x.bv y.bv j).toNat)
    (by
      intro j valid
      rw [←lane_bits_to_nat]
      change (laneBits ty.width j result.bv).toNat = _
      rw [lanes j valid])
  change packLanes (lanetype_Jnn ty.output) (List.map (fun j => laneOfBits (lanetype_Jnn ty.output)
    (narrowLane ty.width signed x.bv y.bv j).toNat) (List.range (128/ty.width))) = _ at packed
  have words : List.map (fun j => laneOfBits (lanetype_Jnn ty.output)
      (narrowLane ty.width signed x.bv y.bv j).toNat) (List.range (128/ty.width)) =
      Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed x.bv) ++
      Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed y.bv) := by
    cases ty <;> with_unfolding_all rfl
  have covers : lsize (lanetype_Jnn ty.output)*(128/ty.width) = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt,words] at packed
  unfold narrowResult
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Narrow Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem narrow_lanes_sound (ty : Spec.Simd.NarrowWidth) (signed : Bool) (x y : U128)
    :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        (Spec.Simd.narrowSource ty signed)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (narrow_lanes ty signed x y)
  intro result lanes
  exact Spec.Simd.narrow_step ty signed x.bv y.bv result.bv
    (narrow_packed ty signed x y result lanes)

theorem narrow_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Spec.Simd.NarrowWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (narrowOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd narrowOpcode
  all_goals with_unfolding_all rfl

@[step] theorem narrow_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Spec.Simd.NarrowWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (narrowOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          (Spec.Simd.narrowSource ty signed)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [narrow_simd_eq floats ty signed offset laneIndex bits x y z memory]
  step with narrow_lanes_sound ty signed x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end
