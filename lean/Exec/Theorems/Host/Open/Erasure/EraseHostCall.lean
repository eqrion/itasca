import Exec.Theorems.Host.Open.Erasure.EraseSegments
noncomputable section
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Exact physical state selected by a root call phase. -/
def acceptCall {M : Type} (select : Selector) (phase : CallPhase M Unit)
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) : State M :=
  match phase with
  | .done answer=>⟨answer.2.2.1,.wasm answer.2.1 answer.1 root results,[]⟩
  | .pending exec store _ address base identity args defaults=>
    ⟨store,.host ⟨0,select identity args.slice,identity,args.slice⟩,[.wasm exec address base root results]⟩

theorem acceptCall_erases {M : Type} (select : Selector) (current : OpenReentrantControl.State M)
    (empty : current.stack=[]) (phase : CallPhase M Unit) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) :
    state (OpenReentrantControl.acceptCall select current phase root results)=acceptCall select phase root results := by
  cases phase <;> simp [OpenReentrantControl.acceptCall,state,acceptCall,empty]

/-- A finite pending-host subtree supplies the actual synchronous callback and
native resume computation, then a strictly shorter standalone Wasm trace. -/
theorem pending_host_trace {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (address : runtime.FuncAddr) (base : Usize)
    (identity : U64) (args defaults : alloc.vec.Vec runtime.Value) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    {count : Nat} {answer : Outcome M}
    (trace : NormalTrace (tick memory floats allocator select) count
      (acceptCall select (.pending exec store () address base identity args defaults) root results) answer) :
    ∃out : Answer M Unit,∃remaining,remaining<count ∧
      resume memory (platform memory floats allocator select) (.pending exec store () address base identity args defaults)=.ok out ∧
      NormalTrace (tick memory floats allocator select) remaining
        ⟨out.2.2.1,.wasm out.2.1 out.1 root results,[]⟩ answer := by
  obtain ⟨taken,terminal,remaining,hostStatus,values,path,modeEq,stackEq,callback,rest,total⟩ :=
    host_task_returns memory floats allocator select trace store identity args.slice defaults.slice
      [.wasm exec address base root results] rfl
  cases rest with
  | done actual=>
    simp only [tick,restore,appendTail,modeEq,stackEq,List.nil_append,OpenReentrantControl.tick,Std.bind_assoc,bind_ok] at actual
    obtain ⟨pair,resumed,packed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
    cases pair
    simp [Std.uncurry,output,state] at packed
  | @next count first middle answer actual rest=>
    simp only [tick,restore,appendTail,modeEq,stackEq,List.nil_append,OpenReentrantControl.tick,Std.bind_assoc,bind_ok] at actual
    obtain ⟨pair,resumed,packed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
    rcases pair with ⟨status,finished⟩
    have middleEq : middle=⟨terminal.store,.wasm finished status root results,[]⟩ := by
      simpa [Std.uncurry,output,state] using packed.symm
    refine ⟨(status,finished,terminal.store,()),count,by omega,?_,?_⟩
    · simp only [resume,callback,Std.uncurry,bind_ok,resumed]
    · simpa only [middleEq] using rest

/-- Completed and pending root phases both factor through the same actual
native call continuation, without a supplied child normality law. -/
theorem call_phase_trace {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (phase : CallPhase M Unit) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    {count : Nat} {answer : Outcome M}
    (trace : NormalTrace (tick memory floats allocator select) count (acceptCall select phase root results) answer) :
    ∃out : Answer M Unit,∃remaining,remaining≤count ∧
      resume memory (platform memory floats allocator select) phase=.ok out ∧
      NormalTrace (tick memory floats allocator select) remaining
        ⟨out.2.2.1,.wasm out.2.1 out.1 root results,[]⟩ answer := by
  cases phase with
  | done out=>exact ⟨out,count,Nat.le_refl _,rfl,trace⟩
  | pending exec store token address base identity args defaults=>
    cases token
    obtain ⟨out,remaining,bound,resumed,rest⟩ := pending_host_trace memory floats allocator select exec store address base identity args defaults root results trace
    exact ⟨out,remaining,Nat.le_of_lt bound,resumed,rest⟩
end Exec.Theorems.OpenReentrantControl.Erased
