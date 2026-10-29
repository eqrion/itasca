import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.SourceMachine.Results

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem return_invocation_result (s : _root_.store) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front results : List val)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (split : f.vals = front ++ results)
    (types : results.map SourceMachine.valueType = f.resultTypes)
    (expected : List valtype)
    (invariant : SourceMachine.InvocationResult expected ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) :
    SourceMachine.InvocationResult expected (returnedState s ambient rest results) := by
  have step : SourceMachine.astep ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ =
      .next (returnedState s ambient rest results) := by
    simpa only [← split] using return_next s ambient f rest after front results types
  exact SourceMachine.instruction_result s ambient f rest .RETURN after _ expected .ret typed invariant step

theorem function_end_invocation_result (s : _root_.store) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩)
    (types : f.vals.map SourceMachine.valueType = f.resultTypes)
    (expected : List valtype)
    (invariant : SourceMachine.InvocationResult expected ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) :
    SourceMachine.InvocationResult expected (returnedState s ambient rest f.vals) := by
  apply SourceMachine.return_frame_result typed invariant
  have length : f.resultTypes.length = f.vals.length := by rw [← types, List.length_map]
  cases rest <;> simp [SourceMachine.returnFrame, SourceMachine.AFrame.arity, length, types, returnedState, SourceMachine.advance]

/-- Returning changes only the caller's operand values, so the fixed source
code bound is retained independently of the returned value contents. -/
theorem returned_state_code_bound {bound : Nat} {s : _root_.store} {ambient : frame}
    {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (bounded : SourceMachine.CodeBound bound ⟨s, ambient, f :: rest, []⟩) (results : List val) :
    SourceMachine.CodeBound bound (returnedState s ambient rest results) := by
  cases rest with
  | nil => exact ⟨bounded.positive, by simp [returnedState, Forall], bounded.functions⟩
  | cons caller rest =>
    refine ⟨bounded.positive, ?_, bounded.functions⟩
    intro frame member
    simp only [returnedState, List.mem_cons] at member
    rcases member with rfl | member
    · exact bounded.frames caller (by simp)
    · exact bounded.frames frame (by simp [member])

end Itasca.Runtime.Interp
