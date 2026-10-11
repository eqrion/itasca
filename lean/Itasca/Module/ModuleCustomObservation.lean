import Itasca.Support.Result
import Itasca.Module.ModuleCustomInvariant

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

/-- A custom-section consumer may change its own state while preserving an
observation, such as the work list handed to deferred compilation threads. -/
def Preserves {V A : Type} (visitor : module.ModuleVisitor V) (observe : V → A) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') → observe v' = observe v

end Itasca.ModuleTail

namespace Itasca

variable {profile : ValidationProfile}

theorem module.validate_tail_with_loop.accepted_preserves {V A : Type}
    (visitor : module.ModuleVisitor V) (observe : V → A) (hp : ModuleTail.Preserves visitor observe)
    (data : Slice U8) (env : module.Env) (v : V)
    (segments : alloc.vec.Vec module.Data) (pos : Usize) (seen : Bool)
    (result : module.Tail) (v' : V)
    (h : module.validate_tail_with_loop visitor data env profile v segments pos seen = .ok (.Ok result, v')) :
    observe v' = observe v := by
  have hinvariant : ModuleTail.PreservesInvariant visitor (fun state => observe state = observe v) := by
    intro before chunk after hcallback hbefore
    exact (hp before chunk after hcallback).trans hbefore
  exact module.validate_tail_with_loop.accepted_invariant visitor _ hinvariant
    data env v segments pos seen result v' h rfl

/-- Accepted tail validation preserves deferred work observations when custom
callbacks do. This speaks only about the actual successful run. -/
theorem module.validate_tail_with.accepted_preserves {V A : Type}
    (visitor : module.ModuleVisitor V) (observe : V → A) (hp : ModuleTail.Preserves visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v : V) (result : module.Tail) (v' : V)
    (h : module.validate_tail_with visitor data pos env profile v = .ok (.Ok result, v')) :
    observe v' = observe v :=
  module.validate_tail_with_loop.accepted_preserves visitor observe hp data env v
    (alloc.vec.Vec.new _) pos false result v' h

end Itasca
