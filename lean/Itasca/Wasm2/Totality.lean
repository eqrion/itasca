import Itasca.Wasm2.Visitor.Total

/-!
# Wasm 2.0 body totality

`Wasm2.emptyVisitorLoop.total` specializes the visitor-generic totality proof to the empty
visitor.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The no-op loop specializes the totality proof for arbitrary returning
visitors; it has no separate termination induction. -/
theorem Wasm2.emptyVisitorLoop.total (data : Slice U8) (env : metadata.Env)
    (profile : ValidationProfile) (locals results : alloc.vec.Vec wasm_types.ValueType)
    (type_index : U32) (st : code.BodyState) (visitor : code.EmptyOpVisitor)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hb : st.blocks.val.length ≤ st.core.pos.val + 1) :
    Wasm2.emptyVisitorLoop data env profile type_index st locals results visitor ⦃ _ => True ⦄ := by
  cases visitor
  obtain ⟨⟨r, v⟩, hr, _⟩ := WP.spec_imp_exists
    (code.body_loop_loop.total
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
      data env ⟨locals, results⟩ type_index profile st () hdata hs ha hb)
  simp [Wasm2.emptyVisitorLoop, hr]

end Itasca
