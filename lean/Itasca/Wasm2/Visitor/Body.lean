import Itasca.Wasm2.Visitor.Transfer

/-!
# Visiting body validation against the empty-visitor validator

Relates `code.validate_body_with`, the body validator with an arbitrary visitor, to the
empty-visitor validator `code.bodyCore`. `eq_core` identifies the empty-visitor run with
`code.bodyCore`, `accepted_erase` and `accepted_lift` give acceptance in both directions, and
`sound` and `complete` lift soundness and completeness to arbitrary accepting visitors.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The empty-visitor run of `code.validate_body_with` is `code.bodyCore`. -/
theorem code.validate_body_with.eq_core (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) :
    (do
      let (r, _) ← code.validate_body_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        data env ctx index profile ()
      .ok r) = code.bodyCore data env ctx.locals ctx.results index profile := by
  unfold code.validate_body_with code.initial_state code.bodyCore
  simp only [Std.bind_assoc]
  split
  · simp
  · simp only [Std.bind_assoc]
    congr 1
    funext i
    split
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp only [Std.bind_assoc]
      congr 1
      funext ft
      congr 1
      funext r
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        cases u
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
        rfl

/-- An accepted visiting body is accepted by the empty-visitor validator, for any result vector
of the scalar context. The source visitor needs no totality assumption. -/
theorem code.validate_body_with.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (results : alloc.vec.Vec wasm_types.ValueType) (v v' : V)
    (h : code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v')) :
    code.bodyCore data env ctx.locals results index profile = .ok (.Ok ()) := by
  obtain ⟨w, hw⟩ := code.validate_body_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data env ctx
    ⟨ctx.locals, results⟩ rfl index profile v () v' h
  cases w
  rw [← code.validate_body_with.eq_core data env ⟨ctx.locals, results⟩]
  simp [hw]

/-- Accepting hooks preserve acceptance by the empty-visitor validator. The scalar context's
result vector does not constrain the signature selected by the type index. -/
theorem code.validate_body_with.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (results : alloc.vec.Vec wasm_types.ValueType) (v : V)
    (h : code.bodyCore data env ctx.locals results index profile = .ok (.Ok ())) :
    ∃ v', code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v') := by
  rw [← code.validate_body_with.eq_core data env ⟨ctx.locals, results⟩] at h
  obtain ⟨⟨r, w⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases w
  simp [Std.uncurry] at h
  subst r
  exact code.validate_body_with.accepted_transfer
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor visitor ha data env
    ⟨ctx.locals, results⟩ ctx rfl index profile () v () hr

/-- Arbitrary accepted visitors establish `Wasm2.Validated` for the profile, without a callback
totality premise. -/
theorem code.validate_body_with.sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (v v' : V)
    (h : code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v')) :
    Wasm2.Validated profile data env ctx.locals index :=
  code.bodyCore.sound data env ctx.locals ctx.results index profile
    (code.validate_body_with.accepted_erase visitor data env ctx index profile _ v v' h)

/-- `Wasm2.Validated` bodies are accepted with accepting callbacks, subject to the
implementation limits. -/
theorem code.validate_body_with.complete {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (henv : Profile.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm2.Validated profile data env ctx.locals index) (v : V) :
    ∃ v', code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v') :=
  code.validate_body_with.accepted_lift visitor ha data env ctx index profile ctx.results v
    (code.bodyCore.complete data env ctx.locals ctx.results index profile henv hsize hbody)

end Itasca
