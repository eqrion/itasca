import Exec.Abs.Core.Bound
import Exec.Abs.Cumulative.Dispatch
import Exec.Abs.FloatCore.Bound
import Exec.Abs.CumulativeState
namespace Exec.Abs.Cumulative
open Exec.Abs.Core

theorem instruction_bound (bound : Nat) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CumulativeInstr op) (typed : FrameTyped s {f with code := op::after} [])
    (bounded : CodeBound bound ⟨s,ambient,{f with code := op::after}::rest,[]⟩)
    (step : instruction s ambient f rest op after = .next next) : CodeBound bound next := by
  have hf := bounded.frames {f with code := op::after} (by simp)
  have ha : sizeOf after ≤ bound := by have hh := hf.1; simp at hh; omega
  have hl := hf.2
  cases covered with
  | core allowed => exact FloatCore.instruction_bound bound s ambient f rest op after next allowed typed bounded step
  | stateful op => rw [stateful_not_core] at step; contradiction
  | indirect_call table type => rw [indirect_not_core] at step; contradiction
  | block bt body valid =>
    simp only [instruction,astep,enterLabel,Bool.false_eq_true,ite_false] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_bound bounded step
      refine ⟨by have hh := hf.1; simp at hh ⊢; omega,?_⟩
      intro label member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ha
      · exact hl label member
  | loop bt body valid =>
    simp only [instruction,astep,enterLabel,ite_true] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_bound bounded step
      refine ⟨by have hh := hf.1; simp at hh ⊢; omega,?_⟩
      intro label member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simpa using hf.1
      · exact hl label member
  | ifelse bt yes no yesValid noValid =>
    simp only [instruction,astep] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_bound bounded step
      refine ⟨?_,hl⟩
      have hh := hf.1
      simp at hh ⊢
      omega


theorem step_bound (bound : Nat) (s next : AState)
    (typed : CoreTyped s) (covered : CumulativeState s) (bounded : CodeBound bound s)
    (step : Core.step s = .next next) : CodeBound bound next := by
  rcases s with ⟨store,ambient,frames,results⟩
  cases frames with
  | nil => simp [Core.step] at step
  | cons frame rest =>
    have empty := typed.typed.activeResults (by simp)
    change results = [] at empty
    subst results
    have allowed := (covered.active frame (by simp)).1
    have frameTyped : FrameTyped store frame [] := by cases typed.typed.frames with | cons head _ => exact head
    have hbounded := bounded.frames frame (by simp)
    cases frame with
    | mk address types locals module labels code values =>
      cases code with
      | cons op after =>
        exact instruction_bound bound store ambient ⟨address,types,locals,module,labels,[],values⟩ rest op after next
          (allowed op (by simp)) frameTyped bounded step
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
end Exec.Abs.Cumulative
