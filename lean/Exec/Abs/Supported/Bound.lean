import Exec.Abs.Core.Bound
import Exec.Abs.Supported.CoreStuck
namespace Exec.Abs.Supported
open Exec.Abs.Core

theorem step_bound (bound : Nat) (s next : AState)
    (typed : CoreTyped s) (covered : SupportedState s) (bounded : CodeBound bound s)
    (step : Core.step s = .next next) : CodeBound bound next := by
  rcases s with ⟨store,ambient,frames,results⟩
  cases frames with
  | nil => simp [Core.step] at step
  | cons frame rest =>
    have empty := typed.typed.activeResults (by simp)
    change results = [] at empty
    subst results
    have supported := (covered.active frame (by simp)).1
    have frameTyped : FrameTyped store frame [] := by cases typed.typed.frames with | cons head _ => exact head
    have hbounded := bounded.frames frame (by simp)
    cases frame with
    | mk address types locals module labels code values =>
      cases code with
      | cons op after =>
        rcases BinaryInstr.core_head (supported op (by simp)) with head | stuck
        · exact Core.instruction_bound bound store ambient ⟨address,types,locals,module,labels,[],values⟩ rest op after next head frameTyped bounded step
        · exact nomatch (stuck _ _ _ _ _).symm.trans step
      | nil =>
        cases labels with
        | nil => exact returnFrame_bound bounded step
        | cons label labels =>
          simp only [Core.step,astep] at step
          split at step
          · apply advance_bound bounded step
            refine ⟨?_,fun l member => hbounded.2 l (by simp [member])⟩
            have hh := hbounded.2 label (by simp)
            have hp := list_size_append label.cont label.after
            have hpos : 1 ≤ sizeOf label.cont := by cases label.cont <;> simp <;> omega
            change sizeOf label.after ≤ bound
            omega
          · contradiction
end Exec.Abs.Supported
