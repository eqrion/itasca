import Itasca.Wasm2.Visitor.Transfer

open Aeneas Aeneas.Std

namespace Itasca

/-- An accepted visiting multi-value body is accepted by the public empty
visitor validator. No totality assumption is required of the source visitor. -/
theorem code.validate_multi_value_body_with.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v v' : V)
    (h : code.validate_multi_value_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    code.validate_multi_value_body data env ctx.locals index = .ok (.Ok ()) := by
  obtain ⟨w, hw⟩ := code.validate_multi_value_body_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data env ctx
    ⟨ctx.locals, alloc.vec.Vec.new _⟩ rfl index v () v' h
  cases w
  simp [code.validate_multi_value_body, hw]

/-- Accepting hooks preserve public multi-value acceptance. The scalar context's
result vector does not constrain the signature selected by the type index. -/
theorem code.validate_multi_value_body_with.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V)
    (h : code.validate_multi_value_body data env ctx.locals index = .ok (.Ok ())) :
    ∃ v', code.validate_multi_value_body_with visitor data env ctx index v = .ok (.Ok (), v') := by
  unfold code.validate_multi_value_body at h
  obtain ⟨⟨r, w⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases w
  simp [Std.uncurry] at h
  subst r
  exact code.validate_multi_value_body_with.accepted_transfer
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor visitor ha data env
    ⟨ctx.locals, alloc.vec.Vec.new _⟩ ctx rfl index () v () hr

/-- Arbitrary accepted visitors establish independent multi-value binary
encoding and generated Wasm 2.0 typing, without a callback totality premise. -/
theorem code.validate_multi_value_body_with.wasm_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v v' : V)
    (h : code.validate_multi_value_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    MultiValue.Validated data env ctx.locals index :=
  code.validate_multi_value_body.wasm_sound data env ctx.locals index
    (code.validate_multi_value_body_with.accepted_erase visitor data env ctx index v v' h)

/-- Independent typing and binary encoding imply actual visiting acceptance,
subject to the implementation limits and accepting callbacks. -/
theorem code.validate_multi_value_body_with.wasm_complete {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32)
    (henv : MultiValue.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : MultiValue.Validated data env ctx.locals index) (v : V) :
    ∃ v', code.validate_multi_value_body_with visitor data env ctx index v = .ok (.Ok (), v') :=
  code.validate_multi_value_body_with.accepted_lift visitor ha data env ctx index v
    (code.validate_multi_value_body.wasm_complete data env ctx.locals index henv hsize hbody)

/-- The visiting body contract combines totality with soundness for its actual
successful result; rejecting callbacks remain ordinary validation errors. -/
theorem code.validate_multi_value_body_with.wasm_spec {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.validate_multi_value_body_with visitor data env ctx index v ⦃ r =>
      r.1 = .Ok () → MultiValue.Validated data env ctx.locals index ⦄ := by
  obtain ⟨⟨r, v'⟩, hr⟩ := code.validate_multi_value_body_with.wasm_total visitor hv data env ctx index v
  rw [hr, WP.spec_ok]
  intro hok
  change r = .Ok () at hok
  subst r
  exact code.validate_multi_value_body_with.wasm_sound visitor data env ctx index v v' hr

end Itasca
