import Exec.Interp.Relations.Normalization
import Exec.Interp.Core.StoreTransport
import Exec.Abs.Core.Typing
namespace Exec.Interp

theorem ErasedStep.core {before after : Abs.AFrame} (step : ErasedStep before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.CoreState ⟨s,ambient,before::rest,[]⟩) :
    Abs.CoreState ⟨s,ambient,after::rest,[]⟩ := by
  cases step with
  | nop f after => exact covered.instruction_tail rfl f.locals f.vals
  | drop f after front value => exact Abs.CoreState.instruction_tail (f := {f with vals := front++[value]}) covered rfl f.locals front
  | block f bt body after front params results signature shape =>
    have current := covered.active _ (List.mem_cons_self ..)
    have bodyCovered := (current.1 _ (List.mem_cons_self ..)).block_body
    apply Abs.core_replace_frame covered
    refine ⟨bodyCovered,?_⟩
    intro label member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by intro i found; simp at found,fun i found => current.1 i (List.mem_cons_of_mem _ found)⟩
    · exact current.2 label member
  | label f label labels =>
    have current := covered.active _ (List.mem_cons_self ..)
    apply Abs.core_replace_frame covered
    exact ⟨(current.2 label (List.mem_cons_self ..)).2,fun outer member => current.2 outer (List.mem_cons_of_mem _ member)⟩

theorem ErasedStep.core_sound {before after : Abs.AFrame} (step : ErasedStep before after)
    (s : store) (ambient : frame) (rest : List Abs.AFrame)
    (typed : Abs.CoreTyped ⟨s,ambient,before::rest,[]⟩) :
    Abs.CoreTyped ⟨s,ambient,after::rest,[]⟩ ∧
    Abs.NextSim ⟨s,ambient,before::rest,[]⟩ ⟨s,ambient,after::rest,[]⟩ := by
  obtain ⟨afterTyped,simulation⟩ := step.sound s ambient rest typed.typed
  exact ⟨⟨afterTyped,typed.contents⟩,simulation⟩

theorem ErasedSteps.core {count before after} (steps : ErasedSteps count before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.CoreState ⟨s,ambient,before::rest,[]⟩) :
    Abs.CoreState ⟨s,ambient,after::rest,[]⟩ := by
  induction steps with
  | nil => exact covered
  | cons step tail ih => exact ih (step.core covered)

end Exec.Interp
