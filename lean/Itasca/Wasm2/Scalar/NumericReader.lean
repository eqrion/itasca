import Itasca.Wasm2.Scalar.ReaderPost
import Itasca.Wasm2.Scalar.Prefix

/-!
Exact numeric-reader effects shared by scalar arithmetic, floating-point operations,
sign extensions, and saturating conversions. Opcode decoding supplies the source
encoding; this proof supplies the common operand and source-prefix preservation.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

theorem Pending.numeric_reader {data env profile locals index st}
    (p : Pending data env profile locals index st) (operation : Numeric.Operation)
    (position : Usize) (capacity : st.core.vals.val.length < Usize.max)
    (encoded : At data p.start (.plain operation.instruction) position)
    (declared : DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) operation.instruction)
    (wasm1 : profile = .Wasm1 → ∀ C, Wasm1.At data p.start (.plain operation.instruction) position ∧
      Wasm1.Instruction C operation.instruction := by intro h; cases h) :
    Numeric.read operation {st.core with pos := position} ⦃ r =>
      r.2.ctrls = st.core.ctrls ∧ r.2.pos = position ∧
      ∀ unit, r.1 = .Ok unit → ∃ values,
        StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        ReaderPost p r.2 operation.instruction p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := position}).val = outer.length := by
    simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic {st.core with pos := position} = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (Numeric.read.segment operation {st.core with pos := position}
    outer p.current.vals vals physicalBase capacity)
  rintro ⟨result,out⟩ ⟨controls,cursor,values,stack,_,numeric⟩
  dsimp only at controls cursor stack numeric ⊢
  refine ⟨controls,cursor,?_⟩
  intro unit accepted
  subst result
  rw [polymorphic] at numeric
  refine ⟨values,numeric,?_⟩
  refine p.append_reader out operation.instruction p.current.ctrl.polymorphic_base values
    operation.wellFormed (cursor ▸ encoded)
    (fun C wf prior => numeric.wasm2_prefix C wf p.current.ops operation.instruction prior
      operation.wellFormed (operation.typed C wf)) ?_ ?_ declared ?_
  · simpa [controls] using ctrls
  · simpa [vals,base] using stack
  · intro hp C
    obtain ⟨bytes, restriction⟩ := wasm1 hp C
    exact ⟨cursor ▸ bytes, restriction⟩

end Itasca.Wasm2
