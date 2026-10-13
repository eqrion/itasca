import Itasca.Wasm1.Step

open Aeneas Aeneas.Std

namespace Itasca

/-- Full Wasm 1.0 body validation on arbitrary bytes. A visitor may reject;
termination requires its hooks to terminate. Acceptance produces independent
binary syntax and the generated SpecTec declarative typing judgment. -/
theorem code.validate_body_with.wasm_spec {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Wasm1.Validated data env ctx bt ⦄ := by
  exact code.validate_body_with.of_wasm_steps visitor data env ctx bt
    (by rw [hresults]; exact Body.initialBlockType_results bt)
    (Wasm1.steps visitor hvisitor data env ctx bt) v

/-- Even an arbitrary caller-supplied result vector cannot cause the extracted
body validator to panic or diverge, provided visitor hooks terminate. -/
theorem code.validate_body_with.wasm_total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v : V) :
    ∃ r, code.validate_body_with visitor data env ctx v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (code.validate_body_with.of_wasm_steps visitor data env ctx
      (Body.initialBlockType ctx.results.val) rfl
      (Wasm1.steps visitor hvisitor data env ctx (Body.initialBlockType ctx.results.val)) v)
  exact ⟨r, hr⟩

theorem code.validate_body_with.wasm_sound_of_total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v v' : V)
    (haccepted : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    Wasm1.Validated data env ctx bt := by
  have hs := code.validate_body_with.wasm_spec visitor hvisitor data env ctx bt hresults v
  simpa [haccepted] using hs

/-- The public non-visiting API has no visitor or valid-input precondition. -/
theorem code.validate_body.wasm_spec (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) :
    code.validate_body data env ctx ⦃ r => r = .Ok () → Wasm1.Validated data env ctx bt ⦄ := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists
    (code.validate_body_with.wasm_spec code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      FullVisitor.empty_total data env ctx bt hresults ())
  simpa [code.validate_body, hr] using hp

theorem code.validate_body.wasm_total (data : Slice U8) (env : module.Env) (ctx : code.Context) :
    ∃ r, code.validate_body data env ctx = .ok r := by
  obtain ⟨⟨r, v⟩, hr⟩ := code.validate_body_with.wasm_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data env ctx ()
  exact ⟨r, by simp [code.validate_body, hr]⟩

theorem code.validate_body.wasm_sound (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (haccepted : code.validate_body data env ctx = .ok (.Ok ())) :
    Wasm1.Validated data env ctx bt := by
  have hs := code.validate_body.wasm_spec data env ctx bt hresults
  simpa [haccepted] using hs

end Itasca
