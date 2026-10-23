import Exec.Interp.StructuredMachine.ReturnStack
import Exec.Interp.StructuredMachine.SupportedBoundarySemantics
import Exec.Interp.StructuredMachine.Execution
import Exec.Interp.Calls.ReturnResult
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem Execution.return_complete {M : Type}
 (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (expected : List valtype)
    (beforePC : Nat) (beforePending : Bool)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected beforePC beforePending)
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw)
    (src count : Nat) (effect : ReturnEffect exec after raw.base.val src count)
    (results : List val) (represented : ValuesAt exec.slots.val (raw.base.val+src) results)
    (types : results.map Code.valueType = f.resultTypes) (width : count = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val+src+count ≤ exec.slots.length)
    (typed : Abs.ATyped (returnedState (Store.decodeStore view code store) ambient rest results))
    (result : Abs.InvocationResult expected (returnedState (Store.decodeStore view code store) ambient rest results)) :
    ∃ pc, Execution view code store after (returnedState (Store.decodeStore view code store) ambient rest results) expected pc false := by
  obtain ⟨stack,ready⟩ := machine.stack.return_complete ambient raw top effect results represented types width bounds
    (fun caller member => machine.typed.typed.heights caller (by simp [member]))
  obtain ⟨pc,cursor⟩ := ready.cursor
  cases rest <;> exact ⟨pc,rfl,⟨typed,machine.typed.contents⟩,StructuredMachine.return_supported machine.core results,result,stack,cursor⟩
end Exec.Interp.StructuredMachine
