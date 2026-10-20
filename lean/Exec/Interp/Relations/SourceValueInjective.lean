import Exec.Interp.Relations.Arguments
import SpecExt.Builtins.Float.Decoding
namespace Exec.Interp
open Aeneas Aeneas.Std

private theorem float32_injective (left right : U32)
    (same : SpecExt.Builtins.floatOfBits 32 left.val=SpecExt.Builtins.floatOfBits 32 right.val) : left=right := by
  have bits := congrArg (SpecExt.Builtins.floatBits 32) same
  rw [SpecExt.Builtins.Float.float_bits_roundtrip_32 left.val (by scalar_tac),
    SpecExt.Builtins.Float.float_bits_roundtrip_32 right.val (by scalar_tac)] at bits
  scalar_tac
private theorem float64_injective (left right : U64)
    (same : SpecExt.Builtins.floatOfBits 64 left.val=SpecExt.Builtins.floatOfBits 64 right.val) : left=right := by
  have bits := congrArg (SpecExt.Builtins.floatBits 64) same
  rw [SpecExt.Builtins.Float.float_bits_roundtrip_64 left.val (by scalar_tac),
    SpecExt.Builtins.Float.float_bits_roundtrip_64 right.val (by scalar_tac)] at bits
  scalar_tac

/-- Source values determine concrete values once reference ownership is fixed.
This retains every floating-point bit pattern, including NaN payloads. -/
theorem sourceValue_injective_owned (owner : Usize) (left right : runtime.Value)
    (leftOwned : OwnedBy owner left) (rightOwned : OwnedBy owner right)
    (same : sourceValue left=sourceValue right) : left=right := by
  have tags : sourceType (rawType left)=sourceType (rawType right) := by
    simpa only [sourceValue_type] using congrArg Code.valueType same
  cases left <;> cases right <;> simp_all [sourceType,rawType,sourceValue,OwnedBy]
  case I32.I32 l r=>congr 1; scalar_tac
  case I64.I64 l r=>congr 1; scalar_tac
  case F32.F32 l r=>exact float32_injective l r same
  case F64.F64 l r=>exact float64_injective l r same
  case V128.V128 l r=>congr 1; scalar_tac
  all_goals
    rename_i l r
    cases l <;> cases r <;> simp_all [sourceValue,OwnedBy]
    all_goals
      rename_i l r
      cases l with | mk ls li=>
        cases r with | mk rs ri=>
          simp_all [sourceValue,OwnedBy]
          congr 2
          scalar_tac

theorem sourceValues_injective_owned (owner : Usize) (left right : List runtime.Value)
    (leftOwned : ∀v∈left,OwnedBy owner v) (rightOwned : ∀v∈right,OwnedBy owner v)
    (same : left.map sourceValue=right.map sourceValue) : left=right := by
  induction left generalizing right with
  | nil=>cases right <;> simpa using same
  | cons head tail ih=>
    cases right with
    | nil=>simp at same
    | cons other rest=>
      have parts := List.cons.inj same
      have headEq := sourceValue_injective_owned owner head other (leftOwned _ (by simp)) (rightOwned _ (by simp)) parts.1
      have tailEq := ih rest (fun v member=>leftOwned v (by simp [member]))
        (fun v member=>rightOwned v (by simp [member])) parts.2
      simp only [headEq,tailEq]

theorem sourceSlice_injective_owned (owner : Usize) (left right : Slice runtime.Value)
    (leftOwned : ∀v∈left.val,OwnedBy owner v) (rightOwned : ∀v∈right.val,OwnedBy owner v)
    (same : left.val.map sourceValue=right.val.map sourceValue) : left=right := by
  apply Slice.ext
  exact sourceValues_injective_owned owner left.val right.val leftOwned rightOwned same
end Exec.Interp
