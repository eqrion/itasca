import Itasca.Wasm1.Step

/-!
# Wasm 1.0 body soundness and totality

Main soundness results for `code.validate_body_with` and `code.validate_body` under Wasm 1.0.
Acceptance gives `Wasm1.Validated`: an independent binary encoding with generated SpecTec typing
(`code.validate_body.wasm_sound`). `code.validate_body.wasm_total` shows the validator never
panics or diverges. The profile-strengthened versions are in `Wasm1/ProfileSoundness`.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.validate_body_with` on arbitrary bytes and a total visitor accepts only bodies that
satisfy `Wasm1.Validated`. -/
theorem code.validate_body_with.wasm_spec {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Wasm1.Validated data env ctx bt ⦄ := by
  exact code.validate_body_with.of_wasm_steps visitor data env ctx bt
    (by rw [hresults]; exact Wasm1.Loop.initialBlockType_results bt)
    (Wasm1.steps visitor hvisitor data env ctx bt) v

/-- For any result vector in the context, `code.validate_body_with` returns without panicking or
diverging, provided the visitor hooks terminate. -/
theorem code.validate_body_with.wasm_total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v : V) :
    ∃ r, code.validate_body_with visitor data env ctx v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (code.validate_body_with.of_wasm_steps visitor data env ctx
      (Wasm1.Loop.initialBlockType ctx.results.val) rfl
      (Wasm1.steps visitor hvisitor data env ctx (Wasm1.Loop.initialBlockType ctx.results.val)) v)
  exact ⟨r, hr⟩

theorem code.validate_body_with.wasm_sound_of_total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v v' : V)
    (haccepted : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    Wasm1.Validated data env ctx bt := by
  have hs := code.validate_body_with.wasm_spec visitor hvisitor data env ctx bt hresults v
  simpa [haccepted] using hs

/-- `code.validate_body` accepts only bodies that satisfy `Wasm1.Validated`. It has no visitor and
no valid-input precondition. -/
theorem code.validate_body.wasm_spec (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) :
    code.validate_body data env ctx ⦃ r => r = .Ok () → Wasm1.Validated data env ctx bt ⦄ := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists
    (code.validate_body_with.wasm_spec code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      FullVisitor.empty_total data env ctx bt hresults ())
  simpa [code.validate_body, hr] using hp

/-- `code.validate_body` returns without panicking or diverging. -/
theorem code.validate_body.wasm_total (data : Slice U8) (env : module.Env) (ctx : code.Context) :
    ∃ r, code.validate_body data env ctx = .ok r := by
  obtain ⟨⟨r, v⟩, hr⟩ := code.validate_body_with.wasm_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data env ctx ()
  exact ⟨r, by simp [code.validate_body, hr]⟩

/-- If `code.validate_body` returns `Ok`, the body satisfies `Wasm1.Validated`. -/
theorem code.validate_body.wasm_sound (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (haccepted : code.validate_body data env ctx = .ok (.Ok ())) :
    Wasm1.Validated data env ctx bt := by
  have hs := code.validate_body.wasm_spec data env ctx bt hresults
  simpa [haccepted] using hs

end Itasca
