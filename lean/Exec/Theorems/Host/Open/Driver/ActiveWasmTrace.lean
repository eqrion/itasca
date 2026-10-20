import Exec.Theorems.Host.Open.Driver.AtomicHistoryBoundary
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Actual active Wasm ticks ending before host control or inactive readback. -/
inductive ActiveWasmTrace {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector) :
    Nat → State M → State M → Prop
  | nil (state) : ActiveWasmTrace memory floats allocator select 0 state state
  | next {count state after last exec root results}
      (mode : state.mode=.wasm exec (.Ok ()) root results) (active : 0<exec.frames.length)
      (actual : tick memory floats allocator select state=.ok (.cont after))
      (tail : ActiveWasmTrace memory floats allocator select count after last) :
      ActiveWasmTrace memory floats allocator select (count+1) state last

theorem ActiveWasmTrace.continuing {M F A : Type} {memory : runtime.platform.MemoryBuffer M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A} {select : Selector}
    {count first last} (trace : ActiveWasmTrace memory floats allocator select count first last) :
    ContinuingTrace (tick memory floats allocator select) count first last := by
  induction trace with
  | nil => exact .nil _
  | next mode active actual tail ih => exact .next actual ih

/-- Any finite actual prefix reaching a Wasm boundary has an active-Wasm-only
prefix to its first such boundary. Later host actions cannot enter this trace. -/
theorem continuing_first_wasm_boundary {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count first last} (trace : ContinuingTrace (tick memory floats allocator select) count first last)
    (exec : runtime.interp.Execution) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : first.mode=.wasm exec (.Ok ()) root results) (boundary : NativeWasmBoundary last) :
    ∃ticks reached,ActiveWasmTrace memory floats allocator select ticks first reached ∧ NativeWasmBoundary reached := by
  classical
  induction trace generalizing exec root results with
  | nil current => exact ⟨0,current,.nil _,boundary⟩
  | @next count current after last actual tail ih =>
    by_cases stopped : NativeWasmBoundary current
    · exact ⟨0,current,.nil _,stopped⟩
    · have active : 0<exec.frames.length := by
        by_contra missing
        apply stopped
        simp only [NativeWasmBoundary,mode]
        exact fun h=>missing h.1
      have frames : exec.frames.len>0#usize := by scalar_tac
      have tickActual:=actual
      simp only [tick,mode,prepareLoop,frames,ite_true,core.result.Result.is_ok,bind_ok,Std.bind_assoc] at actual
      obtain ⟨phase,prepared,equal⟩:=Itasca.ResultFacts.bind_ok_inv _ _ _ actual
      simp only [Result.ok.injEq,ControlFlow.cont.injEq] at equal
      subst after
      cases phase with
      | pending ready store token address base identity args defaults =>
        exact ⟨1,_,.next mode active tickActual (.nil _),trivial⟩
      | done answer =>
        cases status : answer.1 with
        | Err error =>
          refine ⟨1,_,.next mode active tickActual (.nil _),?_⟩
          change ¬ActiveExecution (answer.2.1,answer.2.2.1,(),answer.1)
          rw [status]
          rintro ⟨frames,impossible⟩
          cases impossible
        | Ok unit =>
          cases unit
          obtain ⟨ticks,reached,path,finished⟩:=ih answer.2.1 root results (by simp only [acceptCall,status]) boundary
          exact ⟨ticks+1,reached,.next mode active tickActual path,finished⟩
end Exec.Theorems.OpenReentrantControl
