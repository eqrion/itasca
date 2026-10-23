import Itasca.Support.ControlTranslation

/-!
# Control frames

Control-frame vocabulary over the extracted `code.OpIterState`: `base`, `polymorphic`, and the
structural invariant `Control.Shape`, with specifications for `code.cur_base` and
`code.cur_polymorphic`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- The operand stack base of the innermost frame, or `0` with no frames. -/
def base (st : code.OpIterState) : Usize :=
  match st.ctrls.val.getLast? with
  | none => 0#usize
  | some c => c.value_stack_base

/-- Whether the innermost frame is unreachable; `false` with no frames. -/
def polymorphic (st : code.OpIterState) : Bool :=
  match st.ctrls.val.getLast? with
  | none => false
  | some c => c.polymorphic_base

/-- The structural invariant of the control stack: frame stack bases are ordered and within the
operand stack. -/
structure Shape (st : code.OpIterState) : Prop where
  ordered : st.ctrls.val.Pairwise (fun c d => c.value_stack_base.val ≤ d.value_stack_base.val)
  bounded : ∀ c ∈ st.ctrls.val, c.value_stack_base.val ≤ st.vals.val.length

/-- The current frame base is within the operand stack. -/
theorem Shape.base_le {st : code.OpIterState} (h : Shape st) :
    (base st).val ≤ st.vals.val.length := by
  unfold base
  split
  · simp
  · rename_i c hc
    exact h.bounded c (List.mem_of_getLast? hc)

/-- Truncating the operands to the innermost frame base and marking it polymorphic preserves
`Shape`. -/
theorem Shape.unreachable {st st' : code.OpIterState} (h : Shape st)
    (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hctrls' : st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }])
    (hlen : st'.vals.val.length = c.value_stack_base.val) : Shape st' := by
  have hord := h.ordered
  rw [hctrls, List.pairwise_append] at hord
  constructor
  · simpa [hctrls', List.pairwise_append] using hord
  · intro d hd
    rw [hctrls'] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rw [hlen]
      exact hord.2.2 d hd c (by simp)
    · have heq : d = { c with polymorphic_base := true } := by simpa using hd
      simp [heq, hlen]

end Itasca.Control

namespace Itasca

@[step]
theorem code.cur_base.spec (st : code.OpIterState) :
    code.cur_base st ⦃ (b : Usize) => b = Control.base st ⦄ := by
  rcases List.eq_nil_or_concat' st.ctrls.val with h | ⟨cs, c, h⟩
  · unfold code.cur_base
    have hn : alloc.vec.Vec.len st.ctrls = 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    simp [Control.base, h]
  · unfold code.cur_base
    have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    step*
    simp_all [Control.base]

@[step]
theorem code.cur_polymorphic.spec (st : code.OpIterState) :
    code.cur_polymorphic st ⦃ (b : Bool) => b = Control.polymorphic st ⦄ := by
  rcases List.eq_nil_or_concat' st.ctrls.val with h | ⟨cs, c, h⟩
  · unfold code.cur_polymorphic
    have hn : alloc.vec.Vec.len st.ctrls = 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    simp [Control.polymorphic, h]
  · unfold code.cur_polymorphic
    have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    step*
    simp_all [Control.polymorphic]

end Itasca
