import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Itasca.Support.Result
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

inductive TaskKind where
  | host
  | invocation

def Mode.kind {M : Type} : Mode M → TaskKind
  | .host _ | .hostReturn _ _ => .host
  | .preparing _ | .wasm _ _ _ _ | .invokeReturn _ => .invocation

def Outcome.kind {M : Type} : Outcome M → TaskKind
  | .host _ _ => .host
  | .invocation _ _ => .invocation

/-- A host can await a nested invocation, and Wasm can await a host reply.
The root task kind is retained under arbitrarily deep alternation. -/
inductive StackShape : TaskKind → List Continuation → TaskKind → Prop
  | nil (kind) : StackShape kind [] kind
  | host {tail root} (state : HostState) (next : Nat) (under : StackShape .host tail root) :
      StackShape .invocation (.host state next::tail) root
  | wasm {tail root} (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
      (target : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (under : StackShape .invocation tail root) :
      StackShape .host (.wasm exec address base target results::tail) root

def State.Shape {M : Type} (state : State M) (root : TaskKind) : Prop :=
  StackShape state.mode.kind state.stack root

def OutputShape {M : Type} (root : TaskKind) : ControlFlow (State M) (Outcome M) → Prop
  | .cont next => next.Shape root
  | .done answer => answer.kind=root

theorem acceptCall_shape {M : Type} (select : Selector) (state : State M)
    (phase : Interp.OpenCall.CallPhase M Unit) (target : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (root : TaskKind) (held : StackShape .invocation state.stack root) :
    (acceptCall select state phase target results).Shape root := by
  cases phase with
  | done answer => exact held
  | pending exec store token address base identity args defaults => exact .wasm _ _ _ _ _ held

/-- Native effects cannot manufacture a mismatched continuation or change the
root task. Call/return nesting is a property of actual executable ticks. -/
theorem tick_shape {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (state : State M) (root : TaskKind) (held : state.Shape root)
    (out : ControlFlow (State M) (Outcome M)) (actual : tick memory floats allocator select state=.ok out) :
    OutputShape root out := by
  rcases state with ⟨store,mode,stack,history⟩
  cases mode <;> simp only [State.Shape,Mode.kind] at held
  all_goals cases held
  all_goals unfold tick at actual
  all_goals
    repeat' first
      | (simp only [Std.bind_assoc,bind_ok] at actual)
      | (split at actual)
      | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
         cases value
         try simp only [Std.uncurry] at actual)
      | (simp only [Result.ok.injEq] at actual
         cases actual
         simp only [OutputShape,State.Shape,Mode.kind,Outcome.kind]
         all_goals first
         | exact acceptCall_shape _ _ _ _ _ _ (by repeat' first | assumption | constructor)
         | solve | repeat' first | assumption | rfl | constructor)

theorem initialHost_shape {M : Type} (select : Selector) (store : runtime.store.Store M)
    (identity : U64) (args : Slice runtime.Value) : (initialHost select store identity args).Shape .host := .nil _
end Exec.Theorems.OpenReentrantControl
