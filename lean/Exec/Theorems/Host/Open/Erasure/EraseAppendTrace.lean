import Exec.Theorems.Host.Open.Erasure.EraseSegments
noncomputable section
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std Exec.Interp

theorem continuing_nonterminal {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (current next : State M) (actual : tick memory floats allocator select current=.ok (.cont next)) : Nonterminal current := by
  classical
  by_contra boundary
  obtain ⟨answer,stopped⟩ := boundary_tick memory floats allocator select current boundary
  rw [actual] at stopped
  simp at stopped

/-- A standalone finite host trace embeds as an actual continuing subtree
under a suspended outer caller, stopping just before its native resumption. -/
theorem append_host_trace {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first : State M} (status : HostStatus) (after : runtime.store.Store M) (values : Slice runtime.Value)
    (trace : NormalTrace (tick memory floats allocator select) count first (.host (status,after,values)))
    (shape : Shape first .host) (tail : List Continuation) :
    ContinuingTrace (tick memory floats allocator select) count (appendTail tail first) ⟨after,.hostReturn status values,tail⟩ := by
  induction count generalizing first with
  | zero=>
    cases trace with
    | done actual=>
      have boundary:=done_boundary memory floats allocator select first .host shape _ actual
      obtain ⟨replyStatus,replyValues,modeEq,stackEq⟩ := host_boundary first shape boundary
      have finished : tick memory floats allocator select first=.ok (.done (.host (replyStatus,first.store,replyValues))) := by
        simp [tick,restore,OpenReentrantControl.tick,modeEq,stackEq,output,outcome]
      rw [finished] at actual
      have replyEq : (replyStatus,first.store,replyValues)=(status,after,values) := by simpa using actual
      have statusEq:=congrArg Prod.fst replyEq
      have storeEq:=congrArg (fun r : Reply M=>r.2.1) replyEq
      have valuesEq:=congrArg (fun r : Reply M=>r.2.2) replyEq
      have currentEq : appendTail tail first=⟨after,.hostReturn status values,tail⟩ := by
        cases first with | mk store mode stack=>
          simp only [appendTail] at *
          simp [modeEq,stackEq,statusEq,storeEq,valuesEq]
      rw [currentEq]
      exact .nil _
  | succ count ih=>
    cases trace with
    | next actual rest=>
      have active:=continuing_nonterminal memory floats allocator select first _ actual
      have shifted:=tick_append_tail memory floats allocator select first tail active
      rw [actual,bind_ok] at shifted
      exact .next shifted (ih rest (tick_shape memory floats allocator select first _ .host shape actual))
end Exec.Theorems.OpenReentrantControl.Erased
