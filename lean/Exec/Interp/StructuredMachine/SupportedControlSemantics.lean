import Exec.Interp.StructuredMachine.ControlSemantics
import Exec.Interp.Cumulative.Erased
import Exec.Interp.Core.Erased
import Exec.Interp.Core.OwnershipClosure
import Exec.Abs.Stateful.OwnershipStore
import Exec.Interp.StructuredMachine.SyntaxClosure
import Exec.Abs.Supported.PureCoverage
import Exec.Abs.Supported.CumulativeStep
namespace Exec.Interp

theorem StructuredMachine.SyntaxClosure.supported {before after}
    (closure : StructuredMachine.SyntaxClosure allowed before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.SupportedState allowed ⟨s,ambient,before::rest,[]⟩) :
    Abs.SupportedState allowed ⟨s,ambient,after::rest,[]⟩ :=
  Abs.Supported.replace_frame covered (closure (covered.active _ (List.mem_cons_self ..)))

theorem ErasedStep.supported {before after : Abs.AFrame} (step : ErasedStep before after)
    (language : Abs.Supported.Language allowed)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.SupportedState allowed ⟨s,ambient,before::rest,[]⟩) :
    Abs.SupportedState allowed ⟨s,ambient,after::rest,[]⟩ := by
  cases step with
  | nop f after => exact (StructuredMachine.SyntaxClosure.tail f .NOP after f.locals f.vals).supported covered
  | drop f after front value =>
    exact (StructuredMachine.SyntaxClosure.tail {f with vals := front++[value]} .DROP after f.locals front).supported covered
  | block f bt body after front params results signature shape =>
    have current := covered.active _ (List.mem_cons_self ..)
    have bodyCovered := language.block_body (current.1 _ (List.mem_cons_self ..))
    apply Abs.Supported.replace_frame covered
    refine ⟨bodyCovered,?_⟩
    intro label member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by intro i found; simp at found,fun i found => current.1 i (List.mem_cons_of_mem _ found)⟩
    · exact current.2 label member
  | label f label labels =>
    have current := covered.active _ (List.mem_cons_self ..)
    apply Abs.Supported.replace_frame covered
    exact ⟨(current.2 label (List.mem_cons_self ..)).2,fun outer member => current.2 outer (List.mem_cons_of_mem _ member)⟩

theorem ErasedSteps.supported {count before after} (steps : ErasedSteps count before after)
    (language : Abs.Supported.Language allowed)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (covered : Abs.SupportedState allowed ⟨s,ambient,before::rest,[]⟩) :
    Abs.SupportedState allowed ⟨s,ambient,after::rest,[]⟩ := by
  induction steps with
  | nil => exact covered
  | cons step tail ih => exact ih (step.supported language covered)
end Exec.Interp

namespace Exec.Interp.StructuredMachine

def supportedControlSemantics {allowed : instr → Prop} (language : Abs.Supported.Language allowed) :
    ControlSemantics allowed (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned where
  branch depth := language.cumulative (.of_core (.slice (.br (.mk_uN depth))))
  next_covered typed covered step :=
    (Abs.Cumulative.Step.core step (by intro h; cases h)).next_covered_supported language typed covered
  next_owned typed covered step bounds owned :=
    (Abs.Cumulative.Step.core step (by intro h; cases h)).next_owned_supported language typed covered owned
  next_bound typed covered step bound bounded :=
    (Abs.Cumulative.Step.core step (by intro h; cases h)).next_bound_supported language typed covered bounded
  syntax_preserved closure covered := closure.supported covered
  erased step covered := step.supported language covered
  ownership closure owned := closure.stateful owned

end Exec.Interp.StructuredMachine
