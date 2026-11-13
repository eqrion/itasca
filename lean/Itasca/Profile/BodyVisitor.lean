import Itasca.Profile.Body
import Itasca.Wasm2.Visitor.Body

/-!
# Profile body contracts with visitors

Transfers the `Profile.run` contracts to `code.validate_body_with` for an arbitrary
`code.OpVisitor`: `profile_sound` and `profile_complete` give `Wasm2.Validated` soundness and
completeness.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- If the body validator accepts, the body meets
`Wasm2.Validated`. -/
theorem code.validate_body_with.profile_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (v v' : V)
    (h : code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    Wasm2.Validated data env ctx.locals index :=
  Profile.run.sound data env ctx index
    (code.validate_body_with.accepted_erase visitor data env ctx index _ v v' h)

/-- If the body meets `Wasm2.Validated` and the bounds hold, the body validator accepts with
accepting callbacks. -/
theorem code.validate_body_with.profile_complete {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (v : V)
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm2.Validated data env ctx.locals index) :
    ∃ v', code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v') :=
  code.validate_body_with.accepted_lift visitor ha data env ctx index _ v
    (Profile.run.complete data env ctx index hlimits hsize hbody)

end Itasca
