import Exec.Theorems.Host.Open.Source.State.ActiveTick
import Exec.Theorems.Composition.World.ChosenWorldLoop
import Exec.Interp.Control.LoopPrefix
import Itasca.Support.Result
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A Wasm segment stops before entering real host control or once its native
execution is inactive. Result readback belongs to the following driver tick. -/
def NativeWasmBoundary {M : Type} (state : State M) : Prop :=
  match state.mode with
  | .host _ => True
  | .wasm exec status _ _ => ¬ActiveExecution (exec,state.store,(),status)
  | _ => False

/-- Finite atomic execution supplies a finite open prefix. The first pending
host preparation suspends immediately; its atomic callback is never needed to
construct that prefix. Without a suspension the prefix reaches the atomic end. -/
theorem atomic_history_open_boundary {choices : Spec.SourceChoices} {M F A : Type}
    {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (select : Selector)
    {view : M → Slice U8} {expected : List valtype}
    {before after : ChosenWorld emission allowed M Unit view expected} {count events}
    (historyPath : Spec.Iterations (ChosenWorldTransition choices memory (inert memory) floats allocator) count before events after)
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (stack : List Continuation) (history : List Observation) :
    ∃ticks reached,ContinuingTrace (tick memory floats allocator select) ticks
      ⟨before.machine.store,.wasm before.machine.exec (.Ok ()) root results,stack,history⟩ reached ∧
      (NativeWasmBoundary reached ∨ reached=⟨after.machine.store,.wasm after.machine.exec (.Ok ()) root results,stack,history⟩) := by
  induction historyPath with
  | refl current => exact ⟨0,_,.nil _,Or.inr rfl⟩
  | @cons count first middle last events more edge tail ih =>
    let initial : State M:=⟨first.machine.store,.wasm first.machine.exec (.Ok ()) root results,stack,history⟩
    by_cases active : 0<first.machine.exec.frames.length
    · have actualStep : runtime.interp.step memory (inert memory) floats allocator first.machine.exec first.machine.store ()=
          .ok (.Ok (),middle.machine.exec,middle.machine.store,()) := by
        simpa only [show first.machine.platform=() from Subsingleton.elim _ _,
          show middle.machine.platform=() from Subsingleton.elim _ _] using edge.recorded.edge.actual
      have graph:=erase_step memory (inert memory) floats allocator first.machine.exec first.machine.store ()
      rw [actualStep] at graph
      obtain ⟨phase,prepared,resumed⟩:=Itasca.ResultFacts.bind_ok_inv _ _ _ graph
      have computed:=wasm_active_tick memory floats allocator select initial first.machine.exec root results rfl active phase prepared
      cases phase with
      | done answer =>
        have same : answer=(.Ok (),middle.machine.exec,middle.machine.store,()) := by
          simpa only [resume,Result.ok.injEq] using resumed
        subst answer
        obtain ⟨ticks,reached,path,boundary⟩:=ih
        exact ⟨ticks+1,reached,.next computed path,boundary⟩
      | pending exec store token address base identity args defaults =>
        exact ⟨1,_,.next computed (.nil _),Or.inl trivial⟩
    · refine ⟨0,initial,.nil _,Or.inl ?_⟩
      change ¬ActiveExecution (first.machine.exec,first.machine.store,(),(.Ok () : Status))
      exact fun held=>active held.1
end Exec.Theorems.OpenReentrantControl
