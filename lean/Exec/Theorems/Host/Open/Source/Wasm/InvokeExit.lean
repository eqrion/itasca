import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Root invocation exit emits one matching observation and reaches the source
completed mode. The same final interpretation decodes the native returned store. -/
theorem source_invoke_exit {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (answer : InvokeAnswer M Unit) (mode : native.mode=.invokeReturn answer)
    (sourceMode : source.mode=.invokeReturn (sourceInvocationResult answer.1 answer.2.2.2.2))
    (nativeStack : native.stack=[]) (sourceStack : source.stack=[]) :
    let result:=sourceInvocationResult answer.1 answer.2.2.2.2
    let history:=native.history++[Observation.invokeExit answer.1 answer.2.2.2.2]
    let completed : Spec.OpenExecution.State SourceControl:=⟨source.store,.completed result,[]⟩
    tick memory floats allocator select native=.ok (.done (.invocation answer history)) ∧
      Spec.OpenExecution.Transition (sourceModel view (sourcePublication allocator view) select owner stop)
        source [.invokeExit result] completed ∧ completed.Typed ∧
      completed.store=Store.decodeStore view code answer.2.2.1 ∧
      sourceHistory history=sourceHistory native.history++[.invokeExit result] := by
  dsimp only
  have after := guard.native.2.1
  rw [mode] at after
  have sameStore : answer.2.2.1=native.store:=after.1
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [tick,mode,nativeStack,bind_ok]
  · rcases source with ⟨store,sourceControl,stack⟩
    dsimp only at sourceMode sourceStack
    subst sourceControl
    subst stack
    exact .completeInvoke
  · exact ⟨guard.typed.1,trivial,trivial⟩
  · rw [sameStore]
    exact guard.storeEq
  · simp only [sourceHistory,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,sourceObservation,List.append_nil]
end Exec.Theorems.OpenReentrantControl
