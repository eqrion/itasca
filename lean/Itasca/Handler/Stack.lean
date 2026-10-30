import Itasca.Handler.Unreachable

/-!
# Operand stack primitives

Specifications of the extracted stack helpers used by every instruction handler: `code.push_val`,
`code.pop_stack_type`, `code.pop_with_type`, `code.pop_types` and `code.push_types`. They describe
the effect on `st.vals` at concrete operands, and in polymorphic frames, where popping never
consumes operands or fails.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.push_val` appends one operand. -/
@[step]
theorem code.push_val.spec (st : code.OpIterState) (t : code.StackType)
    (hsize : st.vals.val.length < Usize.max) :
    code.push_val st t ⦃ st' =>
      st'.vals.val = st.vals.val ++ [t] ∧ st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  unfold code.push_val
  step*

/-- A pop with the last operand above the current frame base returns that operand and removes it. -/
@[step]
theorem code.pop_stack_type.above_base (st : code.OpIterState)
    (pre : List code.StackType) (t : code.StackType)
    (hvals : st.vals.val = pre ++ [t])
    (hbase : (Control.base st).val ≤ pre.length) :
    code.pop_stack_type st ⦃ r =>
      r.1 = .Ok t ∧ r.2.vals.val = pre ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨_, hb, rfl⟩ := WP.spec_imp_exists (code.cur_base.spec st)
  have hne : alloc.vec.Vec.len st.vals ≠ Control.base st := by scalar_tac
  simp only [code.pop_stack_type, hb, bind_ok, hne, ↓reduceIte]
  simp [alloc.vec.Vec.pop, hvals]

/-- `code.push_types_loop` appends the remaining types in order. -/
@[step]
theorem code.push_types_loop.spec (st : code.OpIterState)
    (ts : Slice wasm_types.ValueType) (i : Usize)
    (hi : i.val ≤ ts.val.length)
    (hsize : st.vals.val.length + (ts.val.length - i.val) ≤ Usize.max) :
    code.push_types_loop st ts i ⦃ st' =>
      st'.vals.val = st.vals.val ++ (ts.val.drop i.val).map code.StackType.Val ∧
      st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  unfold code.push_types_loop
  apply loop.spec_decr_nat (fun p => ts.val.length - p.2.val)
    (fun p => i.val ≤ p.2.val ∧ p.2.val ≤ ts.val.length ∧
      p.1.vals.val ++ (ts.val.drop p.2.val).map code.StackType.Val =
        st.vals.val ++ (ts.val.drop i.val).map code.StackType.Val ∧
      p.1.vals.val.length + (ts.val.length - p.2.val) ≤ Usize.max ∧
      p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos)
  · rintro ⟨s, j⟩ ⟨hij, hj, hv, hb, hc, hp⟩
    dsimp only at hij hj hv hb hc hp
    unfold code.push_types_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = ts.val.length := by scalar_tac
      simp [heq] at hv
      simp [hv, hc, hp]
    · rename_i hmore
      have hlt : j.val < ts.val.length := by scalar_tac
      have hcapacity : s.vals.val.length < Usize.max := by omega
      step
      step
      step
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try scalar_tac
      rw [st1_post, i2_post, vt_post, ← hv]
      simp only [List.append_assoc, List.singleton_append]
      rw [List.drop_eq_getElem_cons hlt, List.map_cons]
  · exact ⟨Nat.le_refl _, hi, rfl, hsize, rfl, rfl⟩

/-- `code.push_types` appends all the types in order. -/
@[step]
theorem code.push_types.spec (st : code.OpIterState) (ts : Slice wasm_types.ValueType)
    (hsize : st.vals.val.length + ts.val.length ≤ Usize.max) :
    code.push_types st ts ⦃ st' =>
      st'.vals.val = st.vals.val ++ ts.val.map code.StackType.Val ∧
      st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  simpa using code.push_types_loop.spec st ts 0#usize (by simp) (by simpa using hsize)

end Itasca
