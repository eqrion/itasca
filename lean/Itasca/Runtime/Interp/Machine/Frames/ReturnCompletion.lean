import Itasca.Runtime.Interp.Machine.Frames.ReturnStack
import Itasca.Runtime.Interp.Machine.Coverage.SupportedBoundarySemantics
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Calls.ReturnResult

/-!
Completing a return while retaining the execution certificate.

Main declarations: `Execution.return_complete`. A direct consumer is `Interp.Machine.Frames.EpilogueExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem Execution.return_complete {M : Type}
 (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (expected : List valtype)
    (beforePC : Nat) (beforePending : Bool)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected beforePC beforePending)
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw)
    (src count : Nat) (effect : ReturnEffect exec after raw.base.val src count)
    (results : List val) (represented : ValuesAt exec.slots.val (raw.base.val+src) results)
    (types : results.map Compiler.valueType = f.resultTypes) (width : count = Compiler.slots (results.map Compiler.valueType))
    (bounds : raw.base.val+src+count ≤ exec.slots.length)
    (typed : SourceMachine.ATyped (returnedState (Store.decodeStore view code store) ambient rest results))
    (result : SourceMachine.InvocationResult expected (returnedState (Store.decodeStore view code store) ambient rest results)) :
    ∃ pc, Execution view code store after (returnedState (Store.decodeStore view code store) ambient rest results) expected pc false := by
  obtain ⟨stack,ready⟩ := machine.stack.return_complete ambient raw top effect results represented types width bounds
    (fun caller member => machine.typed.typed.heights caller (by simp [member]))
  obtain ⟨pc,cursor⟩ := ready.cursor
  cases rest <;> exact ⟨pc,rfl,⟨typed,machine.typed.contents⟩,Machine.return_supported machine.core results,result,stack,cursor⟩
end Itasca.Runtime.Interp.Machine
