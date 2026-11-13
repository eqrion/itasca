import Itasca.Profile.BodySpec
import Itasca.Wasm2.Completeness

/-!
# Profile body contracts

`Body.iff_validated` identifies `Profile.Body` with `Wasm2.Validated`. `Profile.run` is the visitor-free body validator `code.bodyCore`, with `run.sound` and
`run.complete` stating soundness for `Profile.Body` and completeness under the implementation
bounds.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The body grammar describes Wasm 2.0 body bytes. -/
theorem BodyEncoding.to_wasm2 {profile data ops} (h : BodyEncoding profile data ops) :
    Wasm2.BodyEncoding data ops := h

/-- A valid body is a valid Wasm 2.0 body. -/
theorem Body.to_wasm2 {profile data env locals index} (h : Body profile data env locals index) :
    Body .Wasm2 data env locals index := h

/-- `Profile.Body` is the Wasm 2.0 body certificate. -/
theorem Body.iff_validated (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) :
    Body profile data env locals index ↔ Wasm2.Validated profile data env locals index := Iff.rfl

/-- The visitor-free body validator for a profile. -/
def run (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) :=
  code.bodyCore data env ctx.locals ctx.results index profile

/-- If the body validator accepts, the body meets `Profile.Body`. -/
theorem run.sound (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (haccepted : run profile data env ctx index = .ok (.Ok ())) :
    Body profile data env ctx.locals index :=
  code.bodyCore.sound data env ctx.locals ctx.results index profile haccepted

/-- If the body meets `Profile.Body` and the implementation bounds hold, the body validator
accepts. -/
theorem run.complete (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (hlimits : EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Body profile data env ctx.locals index) :
    run profile data env ctx index = .ok (.Ok ()) := by
  exact code.bodyCore.complete data env ctx.locals ctx.results index profile hlimits hsize
    ((Body.iff_validated profile data env ctx.locals index).mp hbody)

end Itasca.Profile
