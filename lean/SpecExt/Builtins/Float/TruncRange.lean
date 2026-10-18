import SpecExt.Builtins.Float.Convert
import Mathlib.Tactic
namespace SpecExt.Builtins.Float
open SpecExt.Builtins

def magnitudeLimit (width : Nat) (negative signed : Bool) : Nat :=
  if signed then if negative then 2^(width-1) else 2^(width-1)-1 else 2^width-1

def magnitudeBoundary (width : Nat) (negative signed : Bool) : Nat :=
  if signed then if negative then 2^(width-1) else 2^(width-1)-1
  else if negative then 0 else 2^width-1

def magnitudeWithin (width : Nat) (negative signed : Bool) (magnitude : Nat) : Prop :=
  magnitude ≤ magnitudeLimit width negative signed ∧ (negative = true → signed = false → magnitude = 0)

def convertMagnitude (width : Nat) (negative signed saturating : Bool) (magnitude : Nat) : Option iN :=
  let value : Int := if negative then -(magnitude : Int) else magnitude
  if saturating then some (saturate width (if signed then .S else .U) value)
  else
    let lower : Int := if signed then -(2:Int)^(width-1) else 0
    let upper : Int := if signed then (2:Int)^(width-1) else 2^width
    if lower ≤ value ∧ value < upper then some (encodeSigned width value) else none

theorem convertMagnitude_outside (width magnitude : Nat) (negative signed saturating : Bool)
    (validWidth : width = 32 ∨ width = 64) (outside : ¬magnitudeWithin width negative signed magnitude) :
    convertMagnitude width negative signed saturating magnitude =
      if saturating then some (.mk_uN (magnitudeBoundary width negative signed)) else none := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed <;> cases saturating
  all_goals norm_num [convertMagnitude, magnitudeWithin, magnitudeLimit, magnitudeBoundary, saturate, encodeSigned,
    min_def, max_def] at *
  all_goals try split_ifs
  all_goals try simp_all
  all_goals omega

theorem convertMagnitude_inside (width magnitude : Nat) (negative signed saturating : Bool)
    (validWidth : width = 32 ∨ width = 64) (inside : magnitudeWithin width negative signed magnitude) :
    convertMagnitude width negative signed saturating magnitude =
      some (.mk_uN (if negative then (2^width-magnitude) % 2^width else magnitude)) := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed <;> cases saturating
  all_goals norm_num [convertMagnitude, magnitudeWithin, magnitudeLimit, saturate, encodeSigned,
    min_def, max_def] at *
  all_goals try split_ifs
  all_goals try simp_all
  all_goals omega

end SpecExt.Builtins.Float
