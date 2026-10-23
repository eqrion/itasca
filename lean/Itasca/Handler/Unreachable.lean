import Itasca.Handler.Control

/-!
# Unreachable code handling

Specifications of `code.mark_unreachable_loop` and `code.mark_unreachable`, which truncate the
operand stack to the innermost frame base and make that frame polymorphic. In such a frame
`code.pop_stack_type` and `code.pop_with_type` return `Bot` at the base without consuming
operands.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `Vec.pop` returns the last element and removes it. -/
@[step]
theorem vec_pop_spec {T : Type} (allocator : Type) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.pop allocator v ⦃ (r : Option T × alloc.vec.Vec T) =>
      r.1 = v.val.getLast? ∧ r.2.val = v.val.dropLast ⦄ := by
  simp [alloc.vec.Vec.pop]

/-- `code.mark_unreachable_loop` terminates and removes exactly the operands above `base`. -/
@[step]
theorem code.mark_unreachable_loop.spec (st : code.OpIterState) (base : Usize)
    (hbase : base.val ≤ st.vals.val.length) :
    code.mark_unreachable_loop st base ⦃ r =>
      r.1.val = st.vals.val.take base.val ∧ r.1.val.length = base.val ∧
      r.2.1 = st.ctrls ∧ r.2.2 = st.pos ⦄ := by
  unfold code.mark_unreachable_loop
  apply loop.spec_decr_nat (fun s => s.vals.val.length)
    (fun s => base.val ≤ s.vals.val.length ∧
      s.vals.val.take base.val = st.vals.val.take base.val ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos)
  · intro s ⟨hlen, htake, hctrls, hpos⟩
    unfold code.mark_unreachable_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : s.vals.val.length = base.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨by simpa [← heq] using htake, heq, hctrls, hpos⟩
    · rename_i hmore
      have hlt : base.val < s.vals.val.length := by scalar_tac
      step*
      simp_all only [List.length_dropLast]
      refine ⟨by omega, ?_, trivial, trivial, by omega⟩
      simpa [List.dropLast_eq_take, List.take_take,
        Nat.min_eq_left (by omega : base.val ≤ s.vals.val.length - 1)] using htake
  · exact ⟨hbase, rfl, rfl, rfl⟩

/-- `code.mark_unreachable` drops the operands above the innermost frame base and makes only that
frame polymorphic. -/
@[step]
theorem code.mark_unreachable.spec (st : code.OpIterState) (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hbase : c.value_stack_base.val ≤ st.vals.val.length) :
    code.mark_unreachable st ⦃ st' =>
      st'.vals.val = st.vals.val.take c.value_stack_base.val ∧
      st'.vals.val.length = c.value_stack_base.val ∧
      st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      st'.pos = st.pos ⦄ := by
  unfold code.mark_unreachable
  have hb : Control.base st = c.value_stack_base := by simp [Control.base, hctrls]
  step*
  simp_all

/-- With no operands above the frame base, `code.pop_stack_type` returns `Bot` in a polymorphic
frame and `EmptyStack` otherwise, leaving the state unchanged. -/
theorem code.pop_stack_type.at_base (st : code.OpIterState)
    (hbase : alloc.vec.Vec.len st.vals = Control.base st) :
    code.pop_stack_type st = .ok
      (if Control.polymorphic st then (.Ok .Bot, st) else (.Err .EmptyStack, st)) := by
  obtain ⟨_, hb, rfl⟩ := WP.spec_imp_exists (code.cur_base.spec st)
  obtain ⟨_, hp, rfl⟩ := WP.spec_imp_exists (code.cur_polymorphic.spec st)
  cases h : Control.polymorphic st <;> simp [code.pop_stack_type, hb, hbase, hp, h]

end Itasca
