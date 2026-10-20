import Exec.Theorems.Host.Open.Erasure.EraseHostCall
import Exec.Interp.Invocation.OpenNativeInvocation
noncomputable section
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- The invocation modes whose synchronous meaning is an extracted API
computation. Host subtrees are factored through their actual callback method. -/
inductive InvocationTask (M : Type) where
  | preparing (phase : InvokePhase M Unit)
  | wasm (exec : runtime.interp.Execution) (status : Status) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
  | returned (answer : InvokeAnswer M Unit)

def InvocationTask.mode {M : Type} : InvocationTask M → Mode M
  | .preparing phase=>.preparing phase
  | .wasm exec status root results=>.wasm exec status root results
  | .returned answer=>.invokeReturn answer

def InvocationTask.evaluate {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (store : runtime.store.Store M) : InvocationTask M → Result (InvokeAnswer M Unit)
  | .preparing phase=>eraseInvoke memory (platform memory floats allocator select) floats allocator phase
  | .wasm exec status root results=>executeAndReadback memory (platform memory floats allocator select) floats allocator root results (exec,store,(),status)
  | .returned answer=>.ok answer

theorem invocation_return_trace {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (store : runtime.store.Store M) (returned : InvokeAnswer M Unit)
    {count : Nat} {answer : Outcome M}
    (trace : NormalTrace (tick memory floats allocator select) count ⟨store,.invokeReturn returned,[]⟩ answer) :
    answer=.invocation returned := by
  cases trace with
  | done actual=>simpa [tick,restore,OpenReentrantControl.tick,output,outcome] using actual.symm
  | next actual rest=>simp [tick,restore,OpenReentrantControl.tick,output,outcome] at actual

/-- Every finite combined invocation has exactly the native synchronous API
answer under the actual driver Platform. Child callback returns are derived
from smaller enclosing traces; no callback-normality premise is supplied. -/
theorem finite_invocation_erases {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (count : Nat) (store : runtime.store.Store M) (task : InvocationTask M) (answer : Outcome M)
    (trace : NormalTrace (tick memory floats allocator select) count ⟨store,task.mode,[]⟩ answer) :
    ∃returned,answer=.invocation returned ∧ task.evaluate memory floats allocator select store=.ok returned := by
  induction count using Nat.strong_induction_on generalizing store task answer with
  | h count ih=>
    cases task with
    | returned returned=>exact ⟨returned,invocation_return_trace memory floats allocator select store returned trace,rfl⟩
    | preparing phase=>
      cases trace with
      | done actual=>
        have boundary:=done_boundary memory floats allocator select ⟨store,.preparing phase,[]⟩ .invocation (.nil _) answer actual
        exact False.elim (boundary trivial)
      | @next restCount first middle answer actual rest=>
        cases phase with
        | done returned=>
          have middleEq : middle=⟨returned.2.2.1,.invokeReturn returned,[]⟩ := by
            simpa [tick,restore,OpenReentrantControl.tick,InvocationTask.mode,output,state] using actual.symm
          have observed:=invocation_return_trace memory floats allocator select returned.2.2.1 returned (by simpa only [middleEq] using rest)
          exact ⟨returned,observed,rfl⟩
        | waiting phase root results=>
          have entered : tick memory floats allocator select ⟨store,.preparing (.waiting phase root results),[]⟩=
              .ok (.cont (acceptCall select phase root results)) := by
            simp only [tick,restore,OpenReentrantControl.tick,bind_ok,output]
            rw [acceptCall_erases select _ rfl]
          have middleEq : middle=acceptCall select phase root results := by
            simpa only [InvocationTask.mode,entered,Result.ok.injEq,ControlFlow.cont.injEq] using actual.symm
          obtain ⟨out,remaining,bound,resumed,suffix⟩ := call_phase_trace memory floats allocator select phase root results
            (by simpa only [middleEq] using rest)
          obtain ⟨returned,observed,native⟩ := ih remaining (by omega) out.2.2.1 (.wasm out.2.1 out.1 root results) answer suffix
          refine ⟨returned,observed,?_⟩
          simp only [InvocationTask.evaluate,eraseInvoke_waiting,resumed,bind_ok]
          exact native
    | wasm exec status root results=>
      cases trace with
      | done actual=>
        have boundary:=done_boundary memory floats allocator select ⟨store,.wasm exec status root results,[]⟩ .invocation (.nil _) answer actual
        exact False.elim (boundary trivial)
      | @next restCount first middle answer actual rest=>
        simp only [tick,restore,InvocationTask.mode,OpenReentrantControl.tick,bind_tc_eq,Std.bind_assoc,bind_ok] at actual
        obtain ⟨phase,prepared,continued⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
        have interrupts : ∀p,(platform memory floats allocator select).interrupt p=(inert memory).interrupt p := by intro p; rfl
        cases phase with
        | finished finished=>
          simp only [bind_tc_eq,Std.bind_assoc] at continued
          obtain ⟨returned,read,packed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ continued
          have middleEq : middle=⟨returned.2.2.1,.invokeReturn returned,[]⟩ := by
            simpa [Std.uncurry,output,state] using packed.symm
          have observed:=invocation_return_trace memory floats allocator select returned.2.2.1 returned (by simpa only [middleEq] using rest)
          refine ⟨returned,observed,?_⟩
          simp only [InvocationTask.evaluate]
          rw [executeAndReadback_prepare memory (platform memory floats allocator select) (inert memory) floats allocator root results _ interrupts]
          simp only [prepared,bind_ok,read]
        | executing phase=>
          have middleEq : middle=acceptCall select phase root results := by
            simpa only [bind_tc_eq,bind_ok,Result.ok.injEq,ControlFlow.cont.injEq,output,
              acceptCall_erases select ⟨store,.wasm exec status root results,[],[]⟩ rfl] using continued.symm
          obtain ⟨out,remaining,bound,resumed,suffix⟩ := call_phase_trace memory floats allocator select phase root results
            (by simpa only [middleEq] using rest)
          obtain ⟨returned,observed,native⟩ := ih remaining (by omega) out.2.2.1 (.wasm out.2.1 out.1 root results) answer suffix
          refine ⟨returned,observed,?_⟩
          simp only [InvocationTask.evaluate]
          rw [executeAndReadback_prepare memory (platform memory floats allocator select) (inert memory) floats allocator root results _ interrupts]
          simp only [prepared,bind_ok,resumed]
          exact native
end Exec.Theorems.OpenReentrantControl.Erased
