import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.State.Request
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- A missing nested function traps locally, without synthesizing an invocation
entry. Both stores and all suspended callers remain at the same world. -/
theorem source_missing_step {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (host : HostState) (hostSource : SourceHostState) (mode : native.mode=.host host)
    (sourceMode : source.mode=.host (.active hostSource))
    (represented : HostStateRepresents native.store.id hostSource host)
    (index : Usize) (values : Slice PureCallbacks.Literal) (nextPC : Nat)
    (selected : host.code[host.pc]?=some (.invoke index values nextPC)) (outside : ¬index.val<native.store.funcs.length) :
    ∃next nextSource,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource 0 ∧
      Spec.OpenExecution.Transition (sourceModel view (sourcePublication allocator view) select owner stop)
        source [.hostAction] nextSource ∧ next.history=native.history := by
  obtain ⟨actual,action⟩ := source_missing_invoke memory floats allocator view code (sourcePublication allocator view) select
    native host mode hostSource represented index values nextPC selected outside
  let next : State M:={native with mode:=.hostReturn (.Err .Trap) (Slice.new _)}
  let nextSource : Spec.OpenExecution.State SourceControl:={source with mode:=.host (.draft none)}
  have sourceGuard : SourceStateGuard memory allocator view code next nextSource 0 :=
    ⟨guard.invariant,.draft (.Err .Trap) (Slice.new _) (by simp),guard.stack,guard.storeEq⟩
  refine ⟨next,nextSource,actual,sourceGuard,?_,rfl⟩
  rcases source with ⟨s,sourceControl,stack⟩
  dsimp only at sourceMode
  subst sourceControl
  have sameStore : s=Store.decodeStore view code native.store:=guard.storeEq
  subst s
  exact .action action
end Exec.Theorems.OpenReentrantControl
