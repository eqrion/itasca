import Itasca.Profile.BodySpec
import Itasca.Binary.Wasm1.DeclaredReferences
import Itasca.Wasm1.ProfileSoundness
import Itasca.Wasm1.Completeness
import Itasca.Wasm2.Completeness

/-!
# Profile body contracts

`Body.wasm1_iff` and `Body.wasm2_iff` identify `Profile.Body` with the Wasm 1.0 and Wasm 2.0 body
specifications. `Profile.run` selects the visitor-free body validator, with `run.total`,
`run.sound` and `run.complete` stating its totality, soundness for `Profile.Body`, and
completeness under the profile's environment and size bounds.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- For Wasm 1.0, `functionContext` is the frame entered from the translated environment. -/
theorem functionContext_wasm1 {env : module.Env} {ctx : code.Context}
    {ft : types.FuncType} {bt : code.BlockType}
    (hr : ctx.results.val = ft.results.val) (hb : ft.results.val = Control.results bt) :
    functionContext env ctx.locals ft =
      Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt := by
  simp only [functionContext, Wasm2.bodyContext, Wasm1.Frames.enter,
    Wasm1.Frames.Form.label, Control.resultTypes, hb]
  congr 1
  simp only [EnvTranslation.context, hr]

/-- `Profile.Body` for Wasm 1.0 is the Wasm 1.0 body specification. -/
theorem Body.wasm1_iff (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (ft : types.FuncType) (bt : code.BlockType)
    (hi : env.types.val[index.val]? = some ft)
    (hr : ctx.results.val = ft.results.val) (hb : ft.results.val = Control.results bt) :
    Body .Wasm1 data env ctx.locals index ↔ Wasm1.Body data env ctx bt := by
  have hc := functionContext_wasm1 (env := env) hr hb
  have hs : FuncType .Wasm1 ft := by
    change ft.results.val.length ≤ 1
    rw [hb]
    cases bt <;> simp [Control.results]
  constructor
  · rintro ⟨ft', ops, hi', _, he, ht, hp, _⟩
    have heq : ft' = ft := Option.some.inj (hi'.symm.trans hi)
    subst ft'
    refine ⟨ops, he, ?_, ?_⟩
    · change Instrs_ok (functionContext env ctx.locals ft) ops _ at ht
      simpa only [Wasm1.FunctionTyped, hc, Control.resultTypes, hb] using ht
    · change Wasm1.Instructions (functionContext env ctx.locals ft) ops at hp
      exact hc ▸ hp
  · rintro ⟨ops, he, ht, hp⟩
    refine ⟨ft, ops, hi, hs, he, ?_, ?_, he.declared _⟩
    · change Instrs_ok (functionContext env ctx.locals ft) ops _
      simpa only [Wasm1.FunctionTyped, hc, Control.resultTypes, hb] using ht
    · change Wasm1.Instructions (functionContext env ctx.locals ft) ops
      exact hc.symm ▸ hp

/-- `Profile.Body` for Wasm 2.0 is the Wasm 2.0 body specification. -/
theorem Body.wasm2_iff (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) :
    Body .Wasm2 data env locals index ↔ Wasm2.Validated data env locals index := by
  constructor
  · rintro ⟨ft, ops, hi, _, he, ht, _, hd⟩
    exact ⟨ft, ops, hi, he, ht, hd⟩
  · rintro ⟨ft, ops, hi, he, ht, hd⟩
    exact ⟨ft, ops, hi, trivial, he, ht, trivial, hd⟩

/-- The visitor-free body validator for a profile: `code.validate_body` for Wasm 1.0 and
`code.validate_multi_value_body` for Wasm 2.0. -/
def run (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) :=
  match profile with
  | .Wasm1 => code.validate_body data env ctx
  | .Wasm2 => code.validate_multi_value_body data env ctx.locals index

/-- The body validator always returns a result for either profile. -/
theorem run.total (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) : ∃ r, run profile data env ctx index = .ok r := by
  cases profile with
  | Wasm1 => exact code.validate_body.wasm_total data env ctx
  | Wasm2 => exact code.validate_multi_value_body.wasm_total data env ctx.locals index

/-- If the body validator accepts, the body meets `Profile.Body`. -/
theorem run.sound (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (ft : types.FuncType)
    (hi : env.types.val[index.val]? = some ft)
    (hr : ctx.results.val = ft.results.val) (hs : FuncType profile ft)
    (haccepted : run profile data env ctx index = .ok (.Ok ())) :
    Body profile data env ctx.locals index := by
  cases profile with
  | Wasm1 =>
    have hb : ∃ bt, ft.results.val = Control.results bt := by
      change ft.results.val.length ≤ 1 at hs
      cases he : ft.results.val with
      | nil => exact ⟨.Empty, rfl⟩
      | cons t rest =>
        cases rest with
        | nil => exact ⟨.Value t, rfl⟩
        | cons _ _ => simp [he] at hs
    obtain ⟨bt, hb⟩ := hb
    exact (Body.wasm1_iff data env ctx index ft bt hi hr hb).mpr
      (code.validate_body.wasm1_sound data env ctx bt (hr.trans hb) haccepted)
  | Wasm2 =>
    exact (Body.wasm2_iff data env ctx.locals index).mpr
      (code.validate_multi_value_body.wasm_sound data env ctx.locals index haccepted)

/-- If the body meets `Profile.Body` and the environment and size bounds hold, the body validator
accepts. -/
theorem run.complete (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (ft : types.FuncType)
    (hi : env.types.val[index.val]? = some ft)
    (hr : ctx.results.val = ft.results.val)
    (henv : Environment profile env) (hlimits : EnvironmentWithinLimits profile env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Body profile data env ctx.locals index) :
    run profile data env ctx index = .ok (.Ok ()) := by
  cases profile with
  | Wasm1 =>
    have hs := henv.1 ft (List.mem_of_getElem? hi)
    have hb : ∃ bt, ft.results.val = Control.results bt := by
      change ft.results.val.length ≤ 1 at hs
      cases he : ft.results.val with
      | nil => exact ⟨.Empty, rfl⟩
      | cons t rest =>
        cases rest with
        | nil => exact ⟨.Value t, rfl⟩
        | cons _ _ => simp [he] at hs
    obtain ⟨bt, hb⟩ := hb
    exact code.validate_body.wasm_complete data env ctx bt ⟨henv.2, henv.1⟩
      (hr.trans hb) hsize ((Body.wasm1_iff data env ctx index ft bt hi hr hb).mp hbody)
  | Wasm2 =>
    have hcap : Wasm2.EnvironmentWithinLimits env := by
      constructor
      · simpa [FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS,
          limits.MAX_MULTI_VALUE_RESULTS] using hlimits.1
      · simpa [FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS,
          limits.MAX_MULTI_VALUE_RESULTS] using hlimits.2
    exact code.validate_multi_value_body.wasm_complete data env ctx.locals index hcap hsize
      ((Body.wasm2_iff data env ctx.locals index).mp hbody)

end Itasca.Profile
