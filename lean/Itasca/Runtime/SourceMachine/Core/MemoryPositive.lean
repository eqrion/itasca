import Itasca.Runtime.SourceMachine.Core.MemoryAccess
import Itasca.Runtime.SourceMachine.Core.Step
namespace Itasca.Runtime.Abs.Core
open SpecExt
theorem load_step_positive (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Load) (argument : memarg) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩) [] (decode next) := by
  simp only [step] at equation
  rw [instruction_load] at equation
  rcases load_progress s ambient {f with code := op.source argument::after} rest after op argument typed with
    ⟨actual,actualEq,fresh,simulation⟩ | ⟨actualEq,_⟩
  · rw [actualEq] at equation
    cases equation
    exact simulation
  · rw [actualEq] at equation
    contradiction

theorem store_step_positive (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Store) (argument : memarg) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩) [] (decode next) := by
  simp only [step] at equation
  rw [instruction_store] at equation
  rcases store_progress s ambient {f with code := op.source argument::after} rest after op argument typed with
    ⟨actual,actualEq,fresh,extension,simulation⟩ | ⟨actualEq,_⟩
  · rw [actualEq] at equation
    cases equation
    exact simulation
  · rw [actualEq] at equation
    contradiction

end Itasca.Runtime.Abs.Core
