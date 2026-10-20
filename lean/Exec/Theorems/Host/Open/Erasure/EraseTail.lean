import Exec.Theorems.Host.Open.Erasure.EraseHistory
noncomputable section
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std

def appendTail {M : Type} (tail : List Continuation) (current : State M) : State M :=
  {current with stack:=current.stack++tail}

def appendOutput {M : Type} (tail : List Continuation) : ControlFlow (State M) (Outcome M) → ControlFlow (State M) (Outcome M)
  | .cont next=>.cont (appendTail tail next)
  | .done answer=>.done answer

/-- A task boundary is handled separately when factoring the caller stack. -/
def Nonterminal {M : Type} (current : State M) : Prop :=
  match current.mode,current.stack with
  | .hostReturn _ _,[]=>False
  | .invokeReturn _,[]=>False
  | _,_=>True

/-- While a task has not reached its own return boundary, adding suspended
outer callers commutes with each actual physical native computation. -/
theorem tick_append_tail {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) (current : State M) (tail : List Continuation) (active : Nonterminal current) :
    tick memory floats allocator select (appendTail tail current)=
      (do let out←tick memory floats allocator select current
          .ok (appendOutput tail out)) := by
  cases current with | mk store mode stack=>
    cases mode <;> cases stack <;> simp_all only [Nonterminal]
    all_goals simp only [tick,appendTail,restore,OpenReentrantControl.tick,Std.bind_assoc,bind_ok]
    all_goals
      repeat' first
        | rfl
        | (congr 1; funext x)
        | (cases x <;> simp_all [Std.uncurry,Std.bind_assoc,bind_ok,output,outcome,state,appendOutput,appendTail,
            OpenReentrantControl.acceptCall,List.append_assoc,List.cons_append])
        | (split <;> simp_all [Std.uncurry,Std.bind_assoc,bind_ok,output,outcome,state,appendOutput,appendTail,
            OpenReentrantControl.acceptCall,List.append_assoc,List.cons_append])
end Exec.Theorems.OpenReentrantControl.Erased
