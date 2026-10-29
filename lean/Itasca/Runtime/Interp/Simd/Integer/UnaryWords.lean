import Itasca.Runtime.Interp.Simd.Integer.UnaryWord
import Itasca.Runtime.Interp.Simd.Integer.Shift

/-!
Unary integer lane arithmetic and iteration. Specialized all-true, sign-mask and population-count adapters remain separate consumers.
-/

/-! ## Simd Unary Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem integer_unary_loop (width action : U32) (x initial : U128)
    (all : Bool) (signs i : U32) (lower : 8 ≤ width.val) (upper : width.val ≤ 64)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv =
      unaryLane action width.val (laneBits width.val j x.bv))
    (allPrefix : all = unaryAll width.val x.bv i.val)
    (signPrefix : signs.bv = unarySigns width.val x.bv i.val) :
    runtime.interp.simd.integer_unary_lanes_loop x width action initial all signs i ⦃ out =>
      (∀ j, j < 128/width.val → laneBits width.val j out.1.bv =
        unaryLane action width.val (laneBits width.val j x.bv)) ∧
      out.2.1 = unaryAll width.val x.bv (128/width.val) ∧
      out.2.2.bv = unarySigns width.val x.bv (128/width.val) ⦄ := by
  unfold runtime.interp.simd.integer_unary_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.2.2.val)
    (fun p => p.2.2.2.val ≤ 128/width.val ∧
      (∀ j, j < p.2.2.2.val → laneBits width.val j p.1.bv =
        unaryLane action width.val (laneBits width.val j x.bv)) ∧
      p.2.1 = unaryAll width.val x.bv p.2.2.2.val ∧
      p.2.2.1.bv = unarySigns width.val x.bv p.2.2.2.val)
  · rintro ⟨current,all,signs,index⟩ ⟨indexBound,initialized,allEq,signEq⟩
    dsimp only at indexBound initialized allEq signEq
    unfold runtime.interp.simd.integer_unary_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      have countBound : 128/width.val ≤ 16 := Nat.div_le_div_left lower (by decide)
      step with lane_bits x width index (by omega) upper (by omega) as ⟨value,input⟩
      step with signed_bits value width (by omega) upper as ⟨signedValue,signedEq⟩
      step with unary_word_effect action value signedValue as ⟨word,wordEq⟩
      subst word
      step with put_lanes current width index (unaryWord action value signedValue)
        (by omega) upper range as ⟨updated,same,other⟩
      have valueEq : value = ⟨(laneBits width.val index.val x.bv).setWidth 64⟩ :=
        (UScalar.eq_equiv_bv_eq _ _).mpr input
      have signedValueEq : signedValue = ⟨(laneBits width.val index.val x.bv).signExtend 64⟩ := by
        apply (IScalar.eq_equiv_bv_eq _ _).mpr
        have truncated : value.bv.setWidth width.val = laneBits width.val index.val x.bv :=
          (congrArg (BitVec.setWidth width.val) input).trans
            ((BitVec.setWidth_setWidth_of_le _ upper).trans (BitVec.setWidth_eq _))
        exact signedEq.trans (congrArg (BitVec.signExtend 64) truncated)
      have allUpdate : (if all then Result.ok (value != 0#u64) else Result.ok false) =
          Result.ok (all && (value != 0#u64)) := by cases all <;> rfl
      rw [allUpdate,bind_ok]
      step as ⟨last,lastEq⟩
      step as ⟨sign,signValue,signBits⟩
      simp only [lift,bind_ok]
      step as ⟨shifted,shiftedValue,shiftedBits⟩
      try simp only [lift,bind_ok]
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j=index.val
        · subst j
          simpa only [unaryLane,valueEq,signedValueEq] using same
        · exact (other j (lane_range _ _ (by omega)) eq).trans (initialized j (by omega))
      · simp only [nextEq,unaryAll,allEq,valueEq]
      · simp only [nextEq,unarySigns]
        change signs.bv ||| shifted.bv = _
        apply congrArg₂ (· ||| ·) signEq
        have shiftedEq := shiftedBits.trans
          (congrArg (fun b : BitVec 32 => b <<< index.val) (UScalar.cast_bv_eq .U32 sign))
        have signEq2 : sign.bv = (laneBits width.val index.val x.bv).setWidth 64 >>> (width.val-1) :=
          signBits.trans ((congrArg (fun b : BitVec 64 => b >>> last.val) input).trans
            (congrArg (fun n => (laneBits width.val index.val x.bv).setWidth 64 >>> n) lastEq))
        exact shiftedEq.trans (congrArg (fun b : BitVec 64 => b.setWidth 32 <<< index.val) signEq2)
      · omega
    · have finished : index.val=128/width.val := by scalar_tac
      simpa [finished] using And.intro initialized (And.intro allEq signEq)
  · exact ⟨position,initializedPrefix,allPrefix,signPrefix⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Unary -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

inductive UnaryAction where | absolute | negate | population | allTrue | bitmask

def unaryAction : UnaryAction → U32
  | .absolute => 0#u32
  | .negate => 1#u32
  | .population => 2#u32
  | .allTrue => 3#u32
  | .bitmask => 4#u32

def unaryOpcode (ty : Jnn) (action : UnaryAction) : U32 :=
  match ty,action with
  | .I8,.absolute => 96#u32
  | .I8,.negate => 97#u32
  | .I8,.population => 98#u32
  | .I8,.allTrue => 99#u32
  | .I8,.bitmask => 100#u32
  | .I16,.absolute => 128#u32
  | .I16,.negate => 129#u32
  | .I16,.population => 130#u32
  | .I16,.allTrue => 131#u32
  | .I16,.bitmask => 132#u32
  | .I32,.absolute => 160#u32
  | .I32,.negate => 161#u32
  | .I32,.population => 162#u32
  | .I32,.allTrue => 163#u32
  | .I32,.bitmask => 164#u32
  | .I64,.absolute => 192#u32
  | .I64,.negate => 193#u32
  | .I64,.population => 194#u32
  | .I64,.allTrue => 195#u32
  | .I64,.bitmask => 196#u32

def UnaryOutcome (ty : Jnn) (action : UnaryAction) (x result : U128) : Prop :=
  let width := lsize (lanetype_Jnn ty)
  match action with
  | .allTrue => result = UScalar.cast .U128 (UScalar.cast_fromBool .U32 (unaryAll width x.bv (128/width)))
  | .bitmask => result = UScalar.cast .U128 (⟨unarySigns width x.bv (128/width)⟩ : U32)
  | _ => ∀ j, j < 128/width → laneBits width j result.bv =
      unaryLane (unaryAction action) width (laneBits width j x.bv)

@[step] theorem integer_unary_lanes (ty : Jnn) (action : UnaryAction) (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode ty action) x
      ⦃ result => UnaryOutcome ty action x result ⦄ := by
  unfold runtime.interp.simd.integer_unary_lanes
  have opcodeBound : 96 ≤ (unaryOpcode ty action).val := by cases ty <;> cases action <;> decide
  step as ⟨difference,differenceEq⟩
  step as ⟨quotient,quotientEq⟩
  have quotientBound : quotient.val < 32 := by
    cases ty <;> cases action <;> simp only [unaryOpcode] at differenceEq <;> scalar_tac
  step as ⟨width,widthEq,widthBits⟩
  have actualWidth : width = shiftWidth ty := by
    apply UScalar.eq_of_val_eq
    cases ty <;> cases action <;> simp only [unaryOpcode,shiftWidth] at * <;> scalar_tac
  subst width
  step as ⟨selected,selectedEq⟩
  have actualAction : selected = unaryAction action := by
    apply UScalar.eq_of_val_eq
    cases ty <;> cases action <;> simp only [unaryOpcode,unaryAction] at * <;> scalar_tac
  subst selected
  step with integer_unary_loop (shiftWidth ty) (unaryAction action) x 0#u128 true 0#u32 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide) (by cases ty <;> decide)
    (by intro j invalid; change j<0 at invalid; omega) rfl rfl as ⟨result,all,signs,lanes,allEq,signEq⟩
  try dsimp only at lanes allEq signEq ⊢
  cases action
  all_goals simp only [unaryAction,
    show (0#u32=3#u32) ↔ False by decide, show (0#u32=4#u32) ↔ False by decide,
    show (1#u32=3#u32) ↔ False by decide, show (1#u32=4#u32) ↔ False by decide,
    show (2#u32=3#u32) ↔ False by decide, show (2#u32=4#u32) ↔ False by decide,
    show (4#u32=3#u32) ↔ False by decide, ite_false,ite_true,
    lift,bind_ok,WP.spec_ok,UnaryOutcome]
  case absolute | negate | population => cases ty <;> with_unfolding_all exact lanes
  case allTrue =>
    have bridge : ∀ answer : Bool, UScalar.cast_fromBool .U128 answer =
        UScalar.cast .U128 (UScalar.cast_fromBool .U32 answer) := by
      intro answer; cases answer <;> decide
    rw [bridge]
    apply congrArg (fun answer => UScalar.cast .U128 (UScalar.cast_fromBool .U32 answer))
    cases ty <;> with_unfolding_all exact allEq
  case bitmask =>
    apply congrArg (UScalar.cast .U128)
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    cases ty <;> with_unfolding_all exact signEq
end Itasca.Runtime.Interp.Simd

end
