import Exec.Interp.Control.LoopPrefix
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem ContinuingTrace.append {α β : Type} {body : α → Result (ControlFlow α β)}
    {a b c : α} {n m : Nat} (first : ContinuingTrace body n a b)
    (second : ContinuingTrace body m b c) : ContinuingTrace body (n+m) a c := by
  induction first with
  | nil => simpa only [Nat.zero_add] using second
  | next step tail ih => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ContinuingTrace.next step (ih second)

end Exec.Interp
