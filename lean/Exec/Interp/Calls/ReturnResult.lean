import Exec.Interp.Calls.ReturnRefinement
import Exec.Abs.Results

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem return_invocation_result (s : _root_.store) (ambient : frame)
    (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front results : List val)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (split : f.vals = front ++ results)
    (types : results.map Abs.valueType = f.resultTypes)
    (expected : List valtype)
    (invariant : Abs.InvocationResult expected ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) :
    Abs.InvocationResult expected (returnedState s ambient rest results) := by
  have step : Abs.astep ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ =
      .next (returnedState s ambient rest results) := by
    simpa only [← split] using return_next s ambient f rest after front results types
  exact Abs.instruction_result s ambient f rest .RETURN after _ expected .ret typed invariant step

theorem function_end_invocation_result (s : _root_.store) (ambient : frame)
    (f : Abs.AFrame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩)
    (types : f.vals.map Abs.valueType = f.resultTypes)
    (expected : List valtype)
    (invariant : Abs.InvocationResult expected ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) :
    Abs.InvocationResult expected (returnedState s ambient rest f.vals) := by
  apply Abs.returnFrame_result typed invariant
  have length : f.resultTypes.length = f.vals.length := by rw [← types, List.length_map]
  cases rest <;> simp [Abs.returnFrame, Abs.AFrame.arity, length, types, returnedState, Abs.advance]

/-- Returning changes only the caller's operand values, so the fixed source
code bound is retained independently of the returned value contents. -/
theorem returnedState_codeBound {bound : Nat} {s : _root_.store} {ambient : frame}
    {f : Abs.AFrame} {rest : List Abs.AFrame}
    (bounded : Abs.CodeBound bound ⟨s, ambient, f :: rest, []⟩) (results : List val) :
    Abs.CodeBound bound (returnedState s ambient rest results) := by
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
