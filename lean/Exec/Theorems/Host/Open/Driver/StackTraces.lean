import Exec.Theorems.Host.Open.Driver.ReentrantStack
import Exec.Interp.Control.LoopPrefix
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

theorem continuing_shape {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first last : State M} {root : TaskKind}
    (trace : Interp.ContinuingTrace (tick memory floats allocator select) count first last)
    (held : first.Shape root) : last.Shape root := by
  induction trace with
  | nil state => exact held
  | next step tail ih => exact ih (tick_shape memory floats allocator select _ root held _ step)

theorem returned_shape {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    {count : Nat} {first : State M} {answer : Outcome M} {root : TaskKind}
    (trace : Interp.NormalTrace (tick memory floats allocator select) count first answer)
    (held : first.Shape root) : answer.kind=root := by
  induction trace with
  | done step => exact tick_shape memory floats allocator select _ root held _ step
  | next step tail ih => exact ih (tick_shape memory floats allocator select _ root held _ step)

/-- All actual finite prefixes of an entered host retain its root kind. An
invocation cannot escape through the host-facing synchronous adapter. -/
theorem initialHost_return_kind {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (store : runtime.store.Store M) (identity : U64) (args : Slice runtime.Value)
    {count : Nat} {answer : Outcome M}
    (trace : Interp.NormalTrace (tick memory floats allocator select) count (initialHost select store identity args) answer) :
    answer.kind=.host := returned_shape memory floats allocator select trace (initialHost_shape ..)
end Exec.Theorems.OpenReentrantControl
