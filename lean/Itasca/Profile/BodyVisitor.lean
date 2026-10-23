import Itasca.Profile.Body
import Itasca.Wasm2.Visitor.Body
import Itasca.Wasm2.ProfileAgreement

/-!
# Profile body contracts with visitors

Transfers the `Profile.run` contracts to `code.validate_body_with` for an arbitrary
`code.OpVisitor`: `profile_sound` and `profile_complete` give `Profile.Body` soundness and
completeness for both profiles. On a valid Wasm 1.0 body, `wasm1_of_body` gives every visitor the
same result under both profiles.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- If the body validator accepts and the selected signature meets `FuncType`, the body meets
`Profile.Body`. -/
theorem code.validate_body_with.profile_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (ft : types.FuncType) (v v' : V)
    (hi : env.types.val[index.val]? = some ft) (hs : Profile.FuncType profile ft)
    (h : code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v')) :
    Profile.Body profile data env ctx.locals index :=
  Profile.run.sound profile data env ctx index ft hi hs
    (code.validate_body_with.accepted_erase visitor data env ctx index profile _ v v' h)

/-- If the body meets `Profile.Body` and the bounds hold, the body validator accepts with
accepting callbacks. -/
theorem code.validate_body_with.profile_complete {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (profile : ValidationProfile) (v : V)
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Profile.Body profile data env ctx.locals index) :
    ∃ v', code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v') :=
  code.validate_body_with.accepted_lift visitor ha data env ctx index profile _ v
    (Profile.run.complete profile data env ctx index hlimits hsize hbody)

/-- On a valid Wasm 1.0 body within the bounds, the Wasm 1.0 run of any visitor is its Wasm 2.0
run. -/
theorem code.validate_body_with.wasm1_of_body {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v : V) r
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Profile.Body .Wasm1 data env ctx.locals index)
    (h : code.validate_body_with visitor data env ctx index .Wasm2 v = .ok r) :
    code.validate_body_with visitor data env ctx index .Wasm1 v = .ok r :=
  code.validate_body_with.wasm1_of_accepted visitor data env ctx index v r
    (Profile.run.complete .Wasm1 data env ctx index hlimits hsize hbody) h

end Itasca
