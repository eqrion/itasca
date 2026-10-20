import Exec.Theorems.Host.Open.Erasure.EraseTail
import Exec.Theorems.Host.Open.Driver.ReentrantStack
noncomputable section
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

/-- A well-nested task can finish only at its own empty-stack return boundary. -/
theorem tick_done_boundary {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (current : State M) (root : TaskKind) (shape : current.Shape root)
    (answer : Outcome M) (actual : tick memory floats allocator select current=.ok (.done answer)) :
    ¬Erased.Nonterminal (Erased.state current) := by
  cases current with | mk store mode stack history=>
    cases mode <;> simp only [State.Shape,Mode.kind] at shape
    all_goals cases shape
    all_goals try { simp [Erased.Nonterminal,Erased.state]; done }
    all_goals unfold tick at actual
    all_goals
      repeat' first
        | (simp only [Std.bind_assoc,bind_ok] at actual)
        | (split at actual)
        | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
           cases value
           try simp only [Std.uncurry] at actual)
        | (simp [acceptCall] at actual)

namespace Erased

def Shape {M : Type} (current : State M) (root : TaskKind) : Prop := StackShape current.mode.kind current.stack root

theorem tick_shape {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (current next : State M) (root : TaskKind) (shape : Shape current root)
    (actual : tick memory floats allocator select current=.ok (.cont next)) : Shape next root := by
  unfold tick at actual
  obtain ⟨out,called,projected⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  cases out with
  | done answer=>simp [output] at projected
  | cont raw=>
    have equal : state raw=next := by simpa [output] using projected
    rw [←equal]
    exact OpenReentrantControl.tick_shape memory floats allocator select (restore current) root shape (.cont raw) called

theorem done_boundary {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (current : State M) (root : TaskKind) (shape : Shape current root)
    (answer : Outcome M) (actual : tick memory floats allocator select current=.ok (.done answer)) : ¬Nonterminal current := by
  unfold tick at actual
  obtain ⟨out,called,projected⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  cases out with
  | cont raw=>simp [output] at projected
  | done raw=>exact tick_done_boundary memory floats allocator select (restore current) root shape raw called

theorem boundary_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (current : State M) (boundary : ¬Nonterminal current) :
    ∃answer,tick memory floats allocator select current=.ok (.done answer) := by
  cases current with | mk store mode stack=>
    cases mode <;> cases stack <;> simp_all only [Nonterminal,not_true_eq_false,not_false_eq_true]
    all_goals simp [tick,restore,OpenReentrantControl.tick,output,outcome]
end Erased
end Exec.Theorems.OpenReentrantControl
