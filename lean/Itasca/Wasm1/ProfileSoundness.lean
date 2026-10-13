import Itasca.Wasm1.Step
import Itasca.Wasm1.Visitor.Erasure

/-!
# Wasm 1.0 profile soundness

Soundness of `code.validate_body_with` and `code.validate_body` against `Wasm1.Body`, which adds
the Wasm 1.0 profile to the typing of `Wasm1/Soundness`. `code.validate_body.wasm1_sound` is the
main result. Accepted visitor executions reduce to the non-visiting validator by erasure.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Accepted bodies satisfy the Wasm 1.0 profile, including identical `br_table` target
signatures in unreachable code and in all nested blocks. -/
theorem code.validate_body_with.wasm1_spec {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Wasm1.Body data env ctx bt ⦄ := by
  exact code.validate_body_with.of_wasm1_steps visitor data env ctx bt
    (by rw [hresults]; exact Wasm1.Loop.initialBlockType_results bt)
    (Wasm1.steps visitor hvisitor data env ctx bt) v

/-- `code.validate_body` accepts only bodies that satisfy `Wasm1.Body`. -/
theorem code.validate_body.wasm1_spec (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) :
    code.validate_body data env ctx ⦃ r => r = .Ok () → Wasm1.Body data env ctx bt ⦄ := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists
    (code.validate_body_with.wasm1_spec code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      FullVisitor.empty_total data env ctx bt hresults ())
  simpa [code.validate_body, hr] using hp

/-- If `code.validate_body` returns `Ok`, the body satisfies `Wasm1.Body`. -/
theorem code.validate_body.wasm1_sound (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (haccepted : code.validate_body data env ctx = .ok (.Ok ())) :
    Wasm1.Body data env ctx bt := by
  have hs := code.validate_body.wasm1_spec data env ctx bt hresults
  simpa [haccepted] using hs

/-- Any accepted execution of `code.validate_body_with` satisfies `Wasm1.Body`. The visitor
callbacks need no termination or acceptance assumption. -/
theorem code.validate_body_with.wasm1_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v v' : V)
    (haccepted : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    Wasm1.Body data env ctx bt :=
  code.validate_body.wasm1_sound data env ctx bt hresults
    (code.validate_body_with.accepted_erase visitor data env ctx v v' haccepted)

end Itasca
