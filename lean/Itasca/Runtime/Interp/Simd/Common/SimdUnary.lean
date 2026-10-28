import Itasca.Runtime.Interp.Simd.Common.SimdUnaryLoop
import Itasca.Runtime.Interp.Simd.Common.SimdShift
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
