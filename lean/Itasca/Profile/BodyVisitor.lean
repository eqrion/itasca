import Itasca.Profile.Body
import Itasca.Profile.BodyExecution
import Itasca.Wasm2.Visitor.Body
import Itasca.Wasm1.Visitor.Lift

/-!
# Profile body contracts with visitors

Transfers the `Profile.run` contracts to `CodeEntry.runBody` for an arbitrary `code.OpVisitor`:
`accepted_erase` and `accepted_lift` relate acceptance with and without the visitor, and `sound`
and `complete` give `Profile.Body` soundness and completeness for both profiles.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Acceptance with a visitor implies acceptance by the visitor-free validator. -/
theorem CodeEntry.runBody.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v v' : V)
    (h : CodeEntry.runBody visitor profile data env ctx index v = .ok (.Ok (), v')) :
    Profile.run profile data env ctx index = .ok (.Ok ()) := by
  cases profile with
  | Wasm1 => exact code.validate_body_with.accepted_erase visitor data env ctx v v' h
  | Wasm2 => exact code.validate_multi_value_body_with.accepted_erase visitor data env ctx index v v' h

/-- Under `FullVisitor.Accepts`, acceptance by the visitor-free validator implies acceptance with
the visitor. -/
theorem CodeEntry.runBody.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (profile : ValidationProfile)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v : V)
    (h : Profile.run profile data env ctx index = .ok (.Ok ())) :
    ∃ v', CodeEntry.runBody visitor profile data env ctx index v = .ok (.Ok (), v') := by
  cases profile with
  | Wasm1 => exact code.validate_body_with.accepted_lift visitor ha data env ctx v h
  | Wasm2 => exact code.validate_multi_value_body_with.accepted_lift visitor ha data env ctx index v h

/-- If `runBody` accepts, the body meets `Profile.Body`. -/
theorem CodeEntry.runBody.sound {V : Type} (visitor : code.OpVisitor V)
    (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (ft : types.FuncType) (v v' : V)
    (hi : env.types.val[index.val]? = some ft) (hr : ctx.results.val = ft.results.val)
    (hs : Profile.FuncType profile ft)
    (h : CodeEntry.runBody visitor profile data env ctx index v = .ok (.Ok (), v')) :
    Profile.Body profile data env ctx.locals index :=
  Profile.run.sound profile data env ctx index ft hi hr hs
    (CodeEntry.runBody.accepted_erase visitor profile data env ctx index v v' h)

/-- If the body meets `Profile.Body` and the bounds hold, `runBody` accepts. -/
theorem CodeEntry.runBody.complete {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (profile : ValidationProfile)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (ft : types.FuncType) (v : V)
    (hi : env.types.val[index.val]? = some ft) (hr : ctx.results.val = ft.results.val)
    (henv : Profile.Environment profile env) (hlimits : Profile.EnvironmentWithinLimits profile env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Profile.Body profile data env ctx.locals index) :
    ∃ v', CodeEntry.runBody visitor profile data env ctx index v = .ok (.Ok (), v') :=
  CodeEntry.runBody.accepted_lift visitor ha profile data env ctx index v
    (Profile.run.complete profile data env ctx index ft hi hr henv hlimits hsize hbody)

end Itasca
