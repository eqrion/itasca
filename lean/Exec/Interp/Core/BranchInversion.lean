import Exec.Interp.Core.Point
import Exec.Interp.Control.BranchIfInversion
namespace Exec.Interp
open Aeneas.Std

theorem coreEmission_not_br {C before after emitted} {depth : Nat}
    (h : Code.CoreEmission C before (.BR (.mk_uN depth)) emitted after) : False := by
  generalize equality : instr.BR (.mk_uN depth) = instruction at h
  cases h with
  | pure head => exact linearEmission_not_br (by simpa only [←equality] using head)
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]

theorem coreEmission_not_br_if {C before after emitted} {depth : Nat}
    (h : Code.CoreEmission C before (.BR_IF (.mk_uN depth)) emitted after) : False := by
  generalize equality : instr.BR_IF (.mk_uN depth) = instruction at h
  cases h with
  | pure head => exact linearEmission_not_br_if (by simpa only [←equality] using head)
  | _ => simp_all [Abs.Memory.Load.source,Abs.Memory.Store.source]
theorem coreCodeRel_branch_inv {C returns code labels stack pc next output depth after}
    (relation : Code.CoreCodeRel C returns code labels stack
      (.BR (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CoreCodeRel C returns code labels stack (.BR (.mk_uN depth) :: after) target.val next output) ∨
    (∃ label dst src count fragmentEnd,
      labels[depth]? = some label ∧ label.branchLive = true ∧ Code.BranchLayout C.LOCALS stack label dst src count ∧
      Code.Segment code pc (Code.branchInstructions dst src count label.target) fragmentEnd ∧ fragmentEnd ≤ next) := by
  cases relation with
  | linear head fragment rest => exact False.elim (coreEmission_not_br head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branch lookup live layout fragment remaining scope => exact Or.inr ⟨_, _, _, _, _, lookup, live, layout, fragment, remaining⟩


theorem coreCodeRel_branchIf_inv {C returns code labels stack pc next output depth after}
    (relation : Code.CoreCodeRel C returns code labels stack
      (.BR_IF (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CoreCodeRel C returns code labels stack (.BR_IF (.mk_uN depth) :: after) target.val next output) ∨
    (∃ before label dst src count cond resume,
      stack = before ++ [.I32] ∧ labels[depth]? = some label ∧ label.branchLive = true ∧
      Code.BranchLayout C.LOCALS before label dst src count ∧ cond.val = Code.slots C.LOCALS + Code.slots before ∧
      Code.Segment code pc (Code.branchIfInstructions dst src count label.target cond resume) resume.val ∧
      Code.CoreCodeRel C returns code labels before after resume.val next output) := by
  cases relation with
  | linear head fragment rest => exact False.elim (coreEmission_not_br_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branchIf lookup live layout condition fragment rest => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, lookup, live, layout, condition, fragment, rest⟩


end Exec.Interp
