import Exec.Interp.Core.Erased
import Exec.Interp.Core.OwnershipClosure
import Exec.Abs.Stateful.OwnershipStore
import Exec.Interp.StructuredMachine.SyntaxClosure
import Exec.Abs.Cumulative.PureCoverage
namespace Exec.Interp

theorem StructuredMachine.SyntaxClosure.cumulative {before after}
    (closure : StructuredMachine.SyntaxClosure Abs.CumulativeInstr before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.CumulativeState ⟨s,ambient,before::rest,[]⟩) :
    Abs.CumulativeState ⟨s,ambient,after::rest,[]⟩ :=
  Abs.Cumulative.replace_frame covered (closure (covered.active _ (List.mem_cons_self ..)))

theorem ErasedStep.cumulative {before after : Abs.AFrame} (step : ErasedStep before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.CumulativeState ⟨s,ambient,before::rest,[]⟩) :
    Abs.CumulativeState ⟨s,ambient,after::rest,[]⟩ := by
  cases step with
  | nop f after => exact (StructuredMachine.SyntaxClosure.tail f .NOP after f.locals f.vals).cumulative covered
  | drop f after front value =>
    exact (StructuredMachine.SyntaxClosure.tail {f with vals := front++[value]} .DROP after f.locals front).cumulative covered
  | block f bt body after front params results signature shape =>
    have current := covered.active _ (List.mem_cons_self ..)
    have bodyCovered := (current.1 _ (List.mem_cons_self ..)).block_body
    apply Abs.Cumulative.replace_frame covered
    refine ⟨bodyCovered,?_⟩
    intro label member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by intro i found; simp at found,fun i found => current.1 i (List.mem_cons_of_mem _ found)⟩
    · exact current.2 label member
  | label f label labels =>
    have current := covered.active _ (List.mem_cons_self ..)
    apply Abs.Cumulative.replace_frame covered
    exact ⟨(current.2 label (List.mem_cons_self ..)).2,fun outer member => current.2 outer (List.mem_cons_of_mem _ member)⟩

theorem ErasedSteps.cumulative {count before after} (steps : ErasedSteps count before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.CumulativeState ⟨s,ambient,before::rest,[]⟩) :
    Abs.CumulativeState ⟨s,ambient,after::rest,[]⟩ := by
  induction steps with
  | nil => exact covered
  | cons step tail ih => exact ih (step.cumulative covered)
theorem FrameOwnershipClosure.stateful {before after} (closure : FrameOwnershipClosure before after)
    {bounds s ambient rest} (owned : Abs.Ownership.StatefulOwned bounds ⟨s,ambient,before::rest,[]⟩) :
    Abs.Ownership.StatefulOwned bounds ⟨s,ambient,after::rest,[]⟩ := by
  refine ⟨⟨owned.values.1,?_⟩,owned.heap⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact closure bounds (owned.values.2 _ (List.mem_cons_self ..))
  · exact owned.values.2 frame (List.mem_cons_of_mem _ member)

end Exec.Interp
