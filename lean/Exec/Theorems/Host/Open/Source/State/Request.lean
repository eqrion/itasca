import Exec.Theorems.Host.Open.Source.Control.Actions
import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Theorems.Host.Open.Driver.RootInput
import Exec.Spec.Typing.EmptyFrameTyping
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- An absent function traps before any nested-invocation entry is emitted. -/
theorem source_missing_invoke {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (publication : SourcePublication) (select : Selector)
    (state : State M) (host : HostState) (mode : state.mode=.host host) (source : SourceHostState)
    (represented : HostStateRepresents state.store.id source host) (index : Usize)
    (values : Slice PureCallbacks.Literal) (next : Nat)
    (selected : host.code[host.pc]?=some (.invoke index values next)) (outside : ¬index.val<state.store.funcs.length) :
    tick memory floats allocator select state=.ok (.cont {state with mode:=.hostReturn (.Err .Trap) (Slice.new _)}) ∧
    SourceAction view publication (Store.decodeStore view code state.store) (.active source)
      (Store.decodeStore view code state.store) (.draft none) := by
  constructor
  · simp only [tick,mode,selected,if_neg outside]
  · apply SourceAction.missingFunction
    · simpa only [represented.1,represented.2.1] using selected
    · simpa only [Store.decodeStore,List.length_map] using outside
end Exec.Theorems.OpenReentrantControl
