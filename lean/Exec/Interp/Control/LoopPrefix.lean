import Exec.Interp.Control.LoopBasis
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- An exact finite prefix containing only continuing results of the actual
loop body. -/
inductive ContinuingTrace {α β : Type} (body : α → Result (ControlFlow α β)) :
    Nat → α → α → Prop
  | nil (state) : ContinuingTrace body 0 state state
  | next {count state next last} (step : body state = .ok (.cont next))
      (tail : ContinuingTrace body count next last) : ContinuingTrace body (count + 1) state last

end Exec.Interp
