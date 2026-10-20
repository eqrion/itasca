import Exec.Interp.Control.LoopPrefix
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Append a normally returning suffix to an actual continuing prefix. -/
theorem ContinuingTrace.followed_by {α β : Type} {body : α → Result (ControlFlow α β)}
    {first middle : α} {answer : β} {n m : Nat}
    (head : ContinuingTrace body n first middle) (tail : NormalTrace body m middle answer) :
    NormalTrace body (n+m) first answer := by
  induction head with
  | nil=>simpa only [Nat.zero_add] using tail
  | next step rest ih=>simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using NormalTrace.next step (ih tail)
end Exec.Interp
