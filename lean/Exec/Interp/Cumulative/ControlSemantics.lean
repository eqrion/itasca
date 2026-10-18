import Exec.Interp.StructuredMachine.ControlSemantics
import Exec.Interp.Cumulative.Erased
import Exec.Abs.Cumulative.Step
namespace Exec.Interp.Cumulative

/-- Every source obligation of the reusable control machine is discharged by
cumulative syntax and the checked abstract transitions. -/
def controlSemantics : StructuredMachine.ControlSemantics Abs.CumulativeInstr
    Abs.CumulativeState Abs.Ownership.StatefulOwned where
  branch depth := .of_core (.slice (.br (.mk_uN depth)))
  next_covered typed covered step := (Abs.Cumulative.Step.core step (by intro h; cases h)).next_covered typed covered
  next_owned typed covered step bounds owned :=
    (Abs.Cumulative.Step.core step (by intro h; cases h)).next_owned typed covered owned
  next_bound typed covered step bound bounded :=
    (Abs.Cumulative.Step.core step (by intro h; cases h)).next_bound typed covered bounded
  syntax_preserved closure covered := closure.cumulative covered
  erased step covered := step.cumulative covered
  ownership closure owned := closure.stateful owned
end Exec.Interp.Cumulative
