import Itasca.Wasm2.Visitor.Total

/-!
# Wasm 2.0 body totality

`Wasm2.emptyVisitorLoop.total` specializes the visitor-generic totality proof to the empty
visitor. `code.validate_multi_value_body.wasm_total` shows that the extracted body validator
(which validates all of Wasm 2.0) returns a value on every input.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The no-op loop specializes the totality proof for arbitrary returning
visitors; it has no separate termination induction. -/
theorem Wasm2.emptyVisitorLoop.total (data : Slice U8) (env : module.Env)
    (locals results : alloc.vec.Vec types.ValueType) (type_index : U32)
    (st : code.BodyState) (visitor : code.EmptyOpVisitor)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hb : st.blocks.val.length ≤ st.core.pos.val + 1) :
    Wasm2.emptyVisitorLoop data env type_index st locals results visitor ⦃ _ => True ⦄ := by
  cases visitor
  obtain ⟨⟨r, v⟩, hr, _⟩ := WP.spec_imp_exists
    (code.body_loop_loop.wasm2_total
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
      data env ⟨locals, results⟩ type_index st () hdata hs ha hb)
  simp [Wasm2.emptyVisitorLoop, hr]

/-- Every input to the public body validator returns an ordinary
success or validation error, without modeled panic or divergence. No validity
assumption is required of the bytes, environment, locals, or type index. -/
theorem code.validate_multi_value_body.wasm_total (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (type_index : U32) :
    ∃ r, code.validate_multi_value_body data env locals type_index = .ok r := by
  obtain ⟨⟨r, v⟩, hr⟩ := code.validate_multi_value_body_with.wasm_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
    data env ⟨locals, alloc.vec.Vec.new _⟩ type_index ()
  exact ⟨r, by simp [code.validate_multi_value_body, hr]⟩

end Itasca
