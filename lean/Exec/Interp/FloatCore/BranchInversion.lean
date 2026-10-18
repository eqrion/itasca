import Exec.Interp.FloatCore.Linear
import Exec.Interp.Core.BranchInversion
namespace Exec.Interp
open Aeneas.Std

theorem floatCoreEmission_not_br {C before after emitted} {depth : Nat}
    (h : Code.FloatCoreEmission C before (.BR (.mk_uN depth)) emitted after) : False :=
  coreEmission_not_br (h.core_inv rfl)

theorem floatCoreEmission_not_br_if {C before after emitted} {depth : Nat}
    (h : Code.FloatCoreEmission C before (.BR_IF (.mk_uN depth)) emitted after) : False :=
  coreEmission_not_br_if (h.core_inv rfl)
theorem floatCoreCodeRel_branch_inv {C returns code labels stack pc next output depth after}
    (relation : Code.FloatCoreCodeRel C returns code labels stack
      (.BR (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.FloatCoreCodeRel C returns code labels stack (.BR (.mk_uN depth) :: after) target.val next output) ∨
    (∃ label dst src count fragmentEnd,
      labels[depth]? = some label ∧ label.branchLive = true ∧ Code.BranchLayout C.LOCALS stack label dst src count ∧
      Code.Segment code pc (Code.branchInstructions dst src count label.target) fragmentEnd ∧ fragmentEnd ≤ next) := by
  cases relation with
  | linear head fragment rest => exact False.elim (floatCoreEmission_not_br head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branch lookup live layout fragment remaining scope => exact Or.inr ⟨_, _, _, _, _, lookup, live, layout, fragment, remaining⟩


theorem floatCoreCodeRel_branchIf_inv {C returns code labels stack pc next output depth after}
    (relation : Code.FloatCoreCodeRel C returns code labels stack
      (.BR_IF (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.FloatCoreCodeRel C returns code labels stack (.BR_IF (.mk_uN depth) :: after) target.val next output) ∨
    (∃ before label dst src count cond resume,
      stack = before ++ [.I32] ∧ labels[depth]? = some label ∧ label.branchLive = true ∧
      Code.BranchLayout C.LOCALS before label dst src count ∧ cond.val = Code.slots C.LOCALS + Code.slots before ∧
      Code.Segment code pc (Code.branchIfInstructions dst src count label.target cond resume) resume.val ∧
      Code.FloatCoreCodeRel C returns code labels before after resume.val next output) := by
  cases relation with
  | linear head fragment rest => exact False.elim (floatCoreEmission_not_br_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branchIf lookup live layout condition fragment rest => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, lookup, live, layout, condition, fragment, rest⟩


end Exec.Interp
