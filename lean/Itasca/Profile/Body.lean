import Itasca.Profile.BodySpec
import Itasca.Wasm2.Completeness

/-!
# Profile body contracts

`Profile.run` is the visitor-free body validator `code.bodyCore`, with `run.sound`
and `run.complete` stating soundness for `Wasm2.Validated` and completeness under
the implementation bounds.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The body grammar describes Wasm 2.0 body bytes. -/
theorem BodyEncoding.to_wasm2 {data ops} (h : BodyEncoding data ops) :
    Wasm2.BodyEncoding data ops := h

/-- The visitor-free body validator for Wasm 2.0. -/
def run (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) :=
  code.bodyCore data env ctx.locals ctx.results index

/-- If the body validator accepts, the body meets `Wasm2.Validated`. -/
theorem run.sound (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (haccepted : run data env ctx index = .ok (.Ok ())) :
    Wasm2.Validated data env ctx.locals index :=
  code.bodyCore.sound data env ctx.locals ctx.results index haccepted

/-- If the body meets `Wasm2.Validated` and the implementation bounds hold, the body validator
accepts. -/
theorem run.complete (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (hlimits : EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm2.Validated data env ctx.locals index) :
    run data env ctx index = .ok (.Ok ()) := by
  exact code.bodyCore.complete data env ctx.locals ctx.results index hlimits hsize
    hbody

end Itasca.Profile
