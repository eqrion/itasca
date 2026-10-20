import Exec.Theorems.Host.Open.Erasure.EraseShape
noncomputable section
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std

/-- A finite enclosing run supplies an actual retained of the current nested
task up to its own return boundary. This proves finite reentrancy by trace
factorization, rather than imposing a normality law on the child callback. -/
theorem extract_task_prefix {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first : State M} {answer : Outcome M}
    (trace : Interp.NormalTrace (tick memory floats allocator select) count first answer)
    (current : State M) (tail : List Continuation) (same : first=appendTail tail current)
    (root : TaskKind) (shape : Shape current root) :
    ∃retained terminal remaining,Interp.ContinuingTrace (tick memory floats allocator select) retained current terminal ∧
      ¬Nonterminal terminal ∧
      Interp.NormalTrace (tick memory floats allocator select) remaining (appendTail tail terminal) answer ∧
      retained+remaining=count := by
  classical
  induction trace generalizing current with
  | @done first answer actual=>
    by_cases active : Nonterminal current
    · rw [same,tick_append_tail memory floats allocator select current tail active] at actual
      obtain ⟨flow,called,projected⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
      cases flow with
      | cont next=>simp [appendOutput] at projected
      | done result=>exact False.elim (done_boundary memory floats allocator select current root shape result called active)
    · exact ⟨0,current,0,.nil current,active,by simpa only [same] using Interp.NormalTrace.done actual,rfl⟩
  | @next count first middle answer actual rest ih=>
    by_cases active : Nonterminal current
    · have shifted:=actual
      rw [same,tick_append_tail memory floats allocator select current tail active] at shifted
      obtain ⟨flow,called,projected⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ shifted
      cases flow with
      | done result=>exact False.elim (done_boundary memory floats allocator select current root shape result called active)
      | cont next=>
        have nextEq : middle=appendTail tail next := by simpa [appendOutput] using projected.symm
        have nextShape:=tick_shape memory floats allocator select current next root shape called
        obtain ⟨retained,terminal,remaining,path,boundary,restored,total⟩ := ih next nextEq nextShape
        refine ⟨retained+1,terminal,remaining,.next called path,boundary,restored,?_⟩
        omega
    · exact ⟨0,current,count+1,.nil current,active,by simpa only [same] using Interp.NormalTrace.next actual rest,by omega⟩

/-- A factored return boundary supplies a standalone finite task return. -/
theorem task_prefix_returns {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first last : State M}
    (retained : Interp.ContinuingTrace (tick memory floats allocator select) count first last)
    (boundary : ¬Nonterminal last) :
    ∃answer,Interp.NormalTrace (tick memory floats allocator select) count first answer := by
  obtain ⟨answer,actual⟩ := boundary_tick memory floats allocator select last boundary
  refine ⟨answer,?_⟩
  induction retained with
  | nil state=>exact .done actual
  | next step tail ih=>exact .next step (ih boundary actual)


theorem continuing_shape {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first last : State M} {root : TaskKind}
    (trace : Interp.ContinuingTrace (tick memory floats allocator select) count first last)
    (shape : Shape first root) : Shape last root := by
  induction trace with
  | nil=>exact shape
  | next step tail ih=>exact ih (tick_shape memory floats allocator select _ _ root shape step)

theorem host_boundary {M : Type} (current : State M) (shape : Shape current .host) (boundary : ¬Nonterminal current) :
    ∃status values,current.mode=.hostReturn status values ∧ current.stack=[] := by
  cases current with | mk store mode stack=>
    cases mode <;> cases stack <;> simp_all only [Nonterminal,not_true_eq_false,not_false_eq_true]
    all_goals cases shape
    all_goals exact ⟨_,_,by trivial,by trivial⟩

theorem trace_finishes {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first last : State M} {answer : Outcome M}
    (trace : Interp.ContinuingTrace (tick memory floats allocator select) count first last)
    (actual : tick memory floats allocator select last=.ok (.done answer)) :
    Interp.NormalTrace (tick memory floats allocator select) count first answer := by
  induction trace with
  | nil=>exact .done actual
  | next step tail ih=>exact .next step (ih actual)

/-- A finite enclosing interaction derives its nested synchronous callback
return from an actual standalone child trace. No child normality contract is
assumed, and its committed store and values are exactly the saved boundary. -/
theorem host_task_returns {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first : State M} {answer : Outcome M}
    (trace : Interp.NormalTrace (tick memory floats allocator select) count first answer)
    (store : runtime.store.Store M) (identity : U64) (args defaults : Slice runtime.Value)
    (tail : List Continuation)
    (same : first=⟨store,.host ⟨0,select identity args,identity,args⟩,tail⟩) :
    ∃taken terminal remaining status values,
      Interp.ContinuingTrace (tick memory floats allocator select) taken
        ⟨store,.host ⟨0,select identity args,identity,args⟩,[]⟩ terminal ∧
      terminal.mode=.hostReturn status values ∧ terminal.stack=[] ∧
      (platform memory floats allocator select).call_host () store identity args defaults=
        .ok (status,(),terminal.store,values) ∧
      Interp.NormalTrace (tick memory floats allocator select) remaining (appendTail tail terminal) answer ∧
      taken+remaining=count := by
  let current : State M:=⟨store,.host ⟨0,select identity args,identity,args⟩,[]⟩
  obtain ⟨taken,terminal,remaining,path,boundary,rest,total⟩ := extract_task_prefix memory floats allocator select trace current tail same .host (.nil _)
  have shape := continuing_shape memory floats allocator select path (show Shape current .host from .nil _)
  obtain ⟨status,values,modeEq,stackEq⟩ := host_boundary terminal shape boundary
  have finished : tick memory floats allocator select terminal=.ok (.done (.host (status,terminal.store,values))) := by
    simp [tick,restore,OpenReentrantControl.tick,modeEq,stackEq,output,outcome]
  have child:=trace_finishes memory floats allocator select path finished
  obtain ⟨actual,erased,nativeTrace⟩ := lift_normal_trace memory floats allocator select child
    (initialHost select store identity args) rfl
  refine ⟨taken,terminal,remaining,status,values,path,modeEq,stackEq,?_,rest,total⟩
  cases actual with
  | invocation result history=>simp [outcome] at erased
  | host reply history=>
    have replyEq : reply=(status,terminal.store,values) := by simpa [outcome] using erased
    subst reply
    have native:=nativeTrace.result
    change run memory floats allocator select (initialHost select store identity args)=.ok (.host (status,terminal.store,values) history) at native
    simp [platform,native]

end Exec.Theorems.OpenReentrantControl.Erased
