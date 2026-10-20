import Exec.Theorems.Host.Open.Driver.PlatformEffects
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- A particular native callback return exposes the implementation's actual
finite combined trace. This is not a law that every callback invocation returns. -/
theorem callback_return_trace {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (identity : U64) (args defaults : Slice runtime.Value) (status : HostStatus)
    (after : runtime.store.Store M) (values : Slice runtime.Value)
    (actual : (platform memory floats allocator select).call_host () store identity args defaults=.ok (status,(),after,values)) :
    ∃count history,NormalTrace (tick memory floats allocator select) count (initialHost select store identity args)
      (.host (status,after,values) history) := by
  simp only [platform] at actual
  obtain ⟨out,ran,packed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  have safe:=run_safe memory floats allocator correct allocation view laws select code (initialHost select store identity args)
    (initialHost_guard memory view code select store held identity args)
  rw [ran,WP.dspec_ok] at safe
  obtain ⟨count,trace,post⟩ := safe
  have kind:=initialHost_return_kind memory floats allocator select store identity args trace
  cases out with
  | invocation answer history=>cases kind
  | host reply history=>
    rcases reply with ⟨replyStatus,replyStore,replyValues⟩
    have equal : (replyStatus,(),replyStore,replyValues)=(status,(),after,values) := by simpa using packed
    have replyEq:=congrArg (fun answer : HostStatus × Unit × runtime.store.Store M × Slice runtime.Value=>
      (answer.1,answer.2.2.1,answer.2.2.2)) equal
    have outcomeEq:=congrArg (fun reply : Reply M=>Outcome.host reply history) replyEq
    exact ⟨count,history,outcomeEq ▸ trace⟩
end Exec.Theorems.OpenReentrantControl
