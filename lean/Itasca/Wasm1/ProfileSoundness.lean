import Itasca.Wasm1.Step
import Itasca.Wasm1.Visitor.Erasure

open Aeneas Aeneas.Std

namespace Itasca

/-- Accepted bodies obey the independent Wasm 1.0 semantic profile, including
identical branch-table target signatures in unreachable code and all nested arms. -/
theorem code.validate_body_with.wasm1_spec {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Wasm1.Body data env ctx bt ⦄ := by
  exact code.validate_body_with.of_wasm1_steps visitor data env ctx bt
    (by rw [hresults]; exact Body.initialBlockType_results bt)
    (Wasm1.steps visitor hvisitor data env ctx bt) v

theorem code.validate_body.wasm1_spec (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) :
    code.validate_body data env ctx ⦃ r => r = .Ok () → Wasm1.Body data env ctx bt ⦄ := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists
    (code.validate_body_with.wasm1_spec code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      FullVisitor.empty_total data env ctx bt hresults ())
  simpa [code.validate_body, hr] using hp

theorem code.validate_body.wasm1_sound (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (haccepted : code.validate_body data env ctx = .ok (.Ok ())) :
    Wasm1.Body data env ctx bt := by
  have hs := code.validate_body.wasm1_spec data env ctx bt hresults
  simpa [haccepted] using hs

/-- The profile theorem applies to any accepted visitor execution, with no
termination or acceptance assumption on its callbacks. -/
theorem code.validate_body_with.wasm1_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v v' : V)
    (haccepted : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    Wasm1.Body data env ctx bt :=
  code.validate_body.wasm1_sound data env ctx bt hresults
    (code.validate_body_with.accepted_erase visitor data env ctx v v' haccepted)

end Itasca
