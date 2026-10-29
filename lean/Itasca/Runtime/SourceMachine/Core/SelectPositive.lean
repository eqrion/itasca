import Itasca.Runtime.SourceMachine.Core.Select
import Itasca.Runtime.SourceMachine.Core.Step
namespace Itasca.Runtime.SourceMachine.Core
open SpecExt

theorem select_step_positive (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := .SELECT none::after}::rest,[]⟩)
    (step : step ⟨s,ambient,{f with code := .SELECT none::after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := .SELECT none::after}::rest,[]⟩) [] (decode next) := by
  obtain ⟨actual,actualEq,fresh,simulation⟩ := select_progress s ambient {f with code := .SELECT none::after} rest after typed
  change select _ _ _ _ = .next next at step
  rw [actualEq] at step
  cases step
  exact simulation
end Itasca.Runtime.SourceMachine.Core
