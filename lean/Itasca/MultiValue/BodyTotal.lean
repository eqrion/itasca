import Itasca.MultiValue.VisitorTotal

open Aeneas Aeneas.Std

namespace Itasca

/-- The no-op loop specializes the totality proof for arbitrary returning
visitors; it has no separate termination induction. -/
theorem multi_value.validate_body_loop.total (data : Slice U8) (env : module.Env)
    (locals results : alloc.vec.Vec types.ValueType) (type_index : U32)
    (st : multi_value.State) (visitor : code.EmptyOpVisitor)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hb : st.blocks.val.length ≤ st.core.pos.val + 1) :
    multi_value.validate_body_loop data env.types env.imports env.globals env.exports
      env.elements env.start env.func_type_indices env.func_types env.table_types
      env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      type_index st locals results visitor ⦃ _ => True ⦄ := by
  cases visitor
  obtain ⟨⟨r, v⟩, hr, _⟩ := WP.spec_imp_exists
    (multi_value.validate_body_with_loop.total
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
      data env ⟨locals, results⟩ type_index st () hdata hs ha hb)
  simp [multi_value.validate_body_loop, hr]

/-- Every input to the public multi-value body validator returns an ordinary
success or validation error, without modeled panic or divergence. No validity
assumption is required of the bytes, environment, locals, or type index. -/
theorem multi_value.validate_body.wasm_total (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (type_index : U32) :
    ∃ r, multi_value.validate_body data env locals type_index = .ok r := by
  obtain ⟨⟨r, v⟩, hr⟩ := multi_value.validate_body_with.wasm_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
    data env ⟨locals, alloc.vec.Vec.new _⟩ type_index ()
  exact ⟨r, by simp [multi_value.validate_body, hr]⟩

end Itasca
