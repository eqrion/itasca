import Exec.Theorems.Host.Open.Driver.AtomicHistoryBoundary
import Exec.Interp.Control.LoopOpenDivergence
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- An auxiliary atomic loop's finite checked history yields an actual open
prefix to the first suspension or inactive Wasm state. Real host control is
left pending, including when the auxiliary loop used its trapping callback. -/
theorem atomic_loop_open_boundary {choices : Spec.SourceChoices} {M F A : Type}

    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (select : Selector)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : ChosenWorld M Unit view expected) (finalState : ExecutionState M Unit)
    (held : ChosenWorldLoopInvariant choices memory (inert memory) floats allocator Inv initial finalState)
    (stopped : ¬ActiveExecution finalState)
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (stack : List Continuation) (history : List Observation) :
    ∃ticks reached,ContinuingTrace (tick memory floats allocator select) ticks
      ⟨initial.machine.store,.wasm initial.machine.exec (.Ok ()) root results,stack,history⟩ reached ∧ NativeWasmBoundary reached := by
  rcases finalState with ⟨exec,store,token,status⟩
  cases status with
  | Ok unit =>
    cases unit
    simp only [ChosenWorldLoopInvariant] at held
    obtain ⟨current,valid,count,events,path,sameExec,sameStore,sameToken⟩:=held
    obtain ⟨ticks,reached,trace,boundary|rfl⟩:=atomic_history_open_boundary memory floats allocator select path root results stack history
    · exact ⟨ticks,reached,trace,boundary⟩
    · refine ⟨ticks,_,trace,?_⟩
      change ¬ActiveExecution (current.machine.exec,current.machine.store,(),(.Ok () : Status))
      simpa only [sameExec,sameStore,sameToken,show current.machine.platform=() from Subsingleton.elim _ _] using stopped
  | Err error =>
    simp only [ChosenWorldLoopInvariant] at held
    obtain ⟨current,valid,count,events,path,actual,failure⟩:=held
    obtain ⟨ticks,reached,trace,boundary|rfl⟩:=atomic_history_open_boundary memory floats allocator select path root results stack history
    · exact ⟨ticks,reached,trace,boundary⟩
    · let before : State M:=⟨current.machine.store,.wasm current.machine.exec (.Ok ()) root results,stack,history⟩
      by_cases active : 0<current.machine.exec.frames.length
      · have actualStep : runtime.interp.step memory (inert memory) floats allocator current.machine.exec current.machine.store ()=
            .ok (.Err error,exec,store,()) := by
          simpa only [show current.machine.platform=() from Subsingleton.elim _ _,show token=() from Subsingleton.elim _ _] using actual
        have graph:=erase_step memory (inert memory) floats allocator current.machine.exec current.machine.store ()
        rw [actualStep] at graph
        obtain ⟨phase,prepared,resumed⟩:=Itasca.ResultFacts.bind_ok_inv _ _ _ graph
        have computed:=wasm_active_tick memory floats allocator select before current.machine.exec root results rfl active phase prepared
        cases phase with
        | pending ready after nextToken address base identity args defaults =>
          exact ⟨ticks+1,_,trace.append (.next computed (.nil _)),trivial⟩
        | done answer =>
          have same : answer=(.Err error,exec,store,()) := by simpa only [resume,Result.ok.injEq] using resumed
          subst answer
          refine ⟨ticks+1,_,trace.append (.next computed (.nil _)),?_⟩
          change ¬ActiveExecution (exec,store,(),(.Err error : Status))
          rintro ⟨frames,impossible⟩
          cases impossible
      · refine ⟨ticks,before,trace,?_⟩
        change ¬ActiveExecution (current.machine.exec,current.machine.store,(),(.Ok () : Status))
        exact fun h=>active h.1
end Exec.Theorems.OpenReentrantControl
