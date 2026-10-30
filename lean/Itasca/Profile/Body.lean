import Itasca.Profile.BodySpec
import Itasca.Wasm2.Completeness

/-!
# Profile body contracts

`Body.iff_validated` identifies `Profile.Body` with `Wasm2.Validated` and the profile's signature
restriction. `Profile.run` is the visitor-free body validator `code.bodyCore`, with `run.sound` and
`run.complete` stating soundness for `Profile.Body` and completeness under the implementation
bounds.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- Both profile grammars describe Wasm 2.0 body bytes. -/
theorem BodyEncoding.to_wasm2 {profile data ops} (h : BodyEncoding profile data ops) :
    Wasm2.BodyEncoding data ops := by
  cases profile with
  | Wasm1 => exact Wasm1.BodyEncoding.to_wasm2 h
  | Wasm2 => exact h

/-- A valid body of either profile is a valid Wasm 2.0 body. -/
theorem Body.to_wasm2 {profile data env locals index} (h : Body profile data env locals index) :
    Body .Wasm2 data env locals index := by
  obtain ⟨ft, ops, hi, _, he, ht, _, hd⟩ := h
  exact ⟨ft, ops, hi, trivial, he.to_wasm2, ht, trivial, hd⟩

/-- `Profile.Body` is `Wasm2.Validated` for the profile together with `FuncType` for the selected
signature. -/
theorem Body.iff_validated (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) :
    Body profile data env locals index ↔ Wasm2.Validated profile data env locals index ∧
      ∀ ft, env.types.val[index.val]? = some ft → FuncType profile ft := by
  constructor
  · rintro ⟨ft, ops, hi, hs, he, ht, hp, hd⟩
    refine ⟨⟨ft, ops, hi, he.to_wasm2, ht, hd, ?_⟩, fun ft' hi' => ?_⟩
    · intro hp1
      subst hp1
      exact ⟨he, hp⟩
    · have he' : ft' = ft := Option.some.inj (hi'.symm.trans hi)
      subst he'
      exact hs
  · rintro ⟨⟨ft, ops, hi, he, ht, hd, hw⟩, hs⟩
    refine ⟨ft, ops, hi, hs ft hi, ?_, ht, ?_, hd⟩
    · cases profile with
      | Wasm1 => exact (hw rfl).1
      | Wasm2 => exact he
    · cases profile with
      | Wasm1 => exact (hw rfl).2
      | Wasm2 => trivial

/-- The visitor-free body validator for a profile. -/
def run (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) :=
  code.bodyCore data env ctx.locals ctx.results index profile

/-- If the body validator accepts and the selected signature meets `FuncType`, the body meets
`Profile.Body`. -/
theorem run.sound (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (ft : wasm_types.FuncType)
    (hi : env.types.val[index.val]? = some ft) (hs : FuncType profile ft)
    (haccepted : run profile data env ctx index = .ok (.Ok ())) :
    Body profile data env ctx.locals index := by
  refine (Body.iff_validated profile data env ctx.locals index).mpr
    ⟨code.bodyCore.sound data env ctx.locals ctx.results index profile haccepted, fun ft' hi' => ?_⟩
  have he : ft' = ft := Option.some.inj (hi'.symm.trans hi)
  subst he
  exact hs

/-- If the body meets `Profile.Body` and the implementation bounds hold, the body validator
accepts. -/
theorem run.complete (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (hlimits : EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Body profile data env ctx.locals index) :
    run profile data env ctx index = .ok (.Ok ()) := by
  exact code.bodyCore.complete data env ctx.locals ctx.results index profile hlimits hsize
    ((Body.iff_validated profile data env ctx.locals index).mp hbody).1

end Itasca.Profile
