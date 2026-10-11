import Itasca.Profile.Types
import Itasca.Profile.Instructions
import Itasca.Body.Wasm1Soundness
import Itasca.Body.WasmComplete
import Itasca.MultiValue.Complete

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- Exact body bytes, including the final end. This relation does not execute
the validator and does not impose implementation limits. -/
def BodyEncoding (profile : ValidationProfile) (data : Slice U8) (ops : List instr) : Prop :=
  match profile with
  | .Wasm1 => Wasm.BodyEncoding data ops
  | .MultiValue => MultiValue.BodyEncoding data ops

def functionContext (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) : context :=
  Control.labelContext (ft.results.val.map Translate.valueType) ++
    MultiValue.bodyContext env locals ft

/-- A common semantic boundary for function validation. The selected signature
comes from the actual environment; bytes, typing, and version restrictions
refer to the same instruction tree. Resource bounds are separate. -/
def Body (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧ FuncType profile ft ∧
    BodyEncoding profile data ops ∧ MultiValue.FunctionTyped env locals ft ops ∧
    Instructions profile (functionContext env locals ft) ops

theorem functionContext_wasm1 {env : module.Env} {ctx : code.Context}
    {ft : types.FuncType} {bt : code.BlockType}
    (hr : ctx.results.val = ft.results.val) (hb : ft.results.val = Control.results bt) :
    functionContext env ctx.locals ft =
      WasmFrames.enter (EnvTranslation.context env ctx) .body bt := by
  simp only [functionContext, MultiValue.bodyContext, WasmFrames.enter,
    WasmFrames.Form.label, Control.resultTypes, hb]
  congr 1
  simp only [EnvTranslation.context, hr]

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
  · rintro ⟨ft', ops, hi', _, he, ht, hp⟩
    have heq : ft' = ft := Option.some.inj (hi'.symm.trans hi)
    subst ft'
    refine ⟨ops, he, ?_, ?_⟩
    · change Instrs_ok (functionContext env ctx.locals ft) ops _ at ht
      simpa only [Wasm.FunctionTyped, hc, Control.resultTypes, hb] using ht
    · change Wasm1.Instructions (functionContext env ctx.locals ft) ops at hp
      exact hc ▸ hp
  · rintro ⟨ops, he, ht, hp⟩
    refine ⟨ft, ops, hi, hs, he, ?_, ?_⟩
    · change Instrs_ok (functionContext env ctx.locals ft) ops _
      simpa only [Wasm.FunctionTyped, hc, Control.resultTypes, hb] using ht
    · change Wasm1.Instructions (functionContext env ctx.locals ft) ops
      exact hc.symm ▸ hp

theorem Body.multiValue_iff (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) :
    Body .MultiValue data env locals index ↔ MultiValue.Validated data env locals index := by
  constructor
  · rintro ⟨ft, ops, hi, _, he, ht, _⟩
    exact ⟨ft, ops, hi, he, ht⟩
  · rintro ⟨ft, ops, hi, he, ht⟩
    exact ⟨ft, ops, hi, trivial, he, ht, trivial⟩

/-- The no-op body calls selected by the entry pipeline. -/
def run (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) :=
  match profile with
  | .Wasm1 => code.validate_body data env ctx
  | .MultiValue => code.validate_multi_value_body data env ctx.locals index

theorem run.total (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) : ∃ r, run profile data env ctx index = .ok r := by
  cases profile with
  | Wasm1 => exact code.validate_body.wasm_total data env ctx
  | MultiValue => exact code.validate_multi_value_body.wasm_total data env ctx.locals index

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
  | MultiValue =>
    exact (Body.multiValue_iff data env ctx.locals index).mpr
      (code.validate_multi_value_body.wasm_sound data env ctx.locals index haccepted)

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
  | MultiValue =>
    have hcap : MultiValue.EnvironmentWithinLimits env := by
      constructor
      · simpa [FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS,
          limits.MAX_MULTI_VALUE_RESULTS] using hlimits.1
      · simpa [FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS,
          limits.MAX_MULTI_VALUE_RESULTS] using hlimits.2
    exact code.validate_multi_value_body.wasm_complete data env ctx.locals index hcap hsize
      ((Body.multiValue_iff data env ctx.locals index).mp hbody)

end Itasca.Profile
