import Itasca.Wasm2.Scalar.BasicReader

/-!
Shared exact source-prefix and operand facts for drop and untyped select.
Validator preservation and compiler inversion project the same reader result,
including polymorphic operands and the concrete/bottom select result.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

theorem Pending.read_drop {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP) :
    code.read_drop st.core ⦃ r => ∀ value, r.1 = .Ok value → ∃ values,
      StackSemantics.Popped p.current.ctrl.polymorphic_base p.current.vals value values ∧
      ReaderPost p r.2 .DROP p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.pop_stack_type.segment st.core outer p.current.vals vals physicalBase)
  rintro ⟨res,out⟩ ⟨controls, position, values, stack, effect⟩ value accepted
  dsimp only at controls position stack effect accepted ⊢
  subst res
  change StackSemantics.Popped (Control.polymorphic st.core) p.current.vals value values at effect
  rw [polymorphic] at effect
  refine ⟨values, effect, ?_⟩
  have encoded : Wasm1.At data p.start (.plain .DROP) out.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte)
      (by simpa [position] using p.pos) .drop
  refine p.append_reader out .DROP p.current.ctrl.polymorphic_base values .instr_case_2 (.plain encoded)
    (fun C wf prior => effect.wasm2_prefix_drop C wf p.current.ops prior) ?_ ?_ (encoded.declared _)
    (fun _ C => ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; simp [global_simps]) C⟩)
  · simpa [controls] using ctrls
  · simpa [vals, base] using stack

theorem Pending.read_select {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_SELECT) :
    code.read_select st.core ⦃ r => ∀ value, r.1 = .Ok value → ∃ values,
      StackSemantics.SelectEffect p.current.ctrl.polymorphic_base p.current.vals value values ∧
      ReaderPost p r.2 (.SELECT none) p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.read_select.segment st.core outer p.current.vals vals physicalBase capacity)
  rintro ⟨res,out⟩ ⟨controls, position, values, stack, _, effect⟩ value accepted
  dsimp only at controls position stack effect accepted ⊢
  subst res
  change StackSemantics.SelectEffect (Control.polymorphic st.core) p.current.vals value values at effect
  rw [polymorphic] at effect
  refine ⟨values, effect, ?_⟩
  have encoded : Wasm1.At data p.start (.plain (.SELECT none)) out.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte)
      (by simpa [position] using p.pos) .select
  refine p.append_reader out (.SELECT none) p.current.ctrl.polymorphic_base values (.instr_case_3 _) (.plain encoded)
    (fun C wf prior => effect.wasm2_prefix C wf p.current.ops prior) ?_ ?_ (encoded.declared _)
    (fun _ C => ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; simp [global_simps]) C⟩)
  · simpa [controls] using ctrls
  · simpa [vals, base] using stack

end Itasca.Wasm2
