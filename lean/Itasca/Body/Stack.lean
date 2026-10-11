import Itasca.Body.Unreachable

open Aeneas Aeneas.Std

namespace Itasca

@[step]
theorem code.push_val.spec (st : code.OpIterState) (t : code.StackType)
    (hsize : st.vals.val.length < Usize.max) :
    code.push_val st t ⦃ st' =>
      st'.vals.val = st.vals.val ++ [t] ∧ st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  unfold code.push_val
  step*

/-- A pop above the current frame consumes exactly the last operand. -/
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

/-- Concrete operands must match their expected type. -/
@[step]
theorem code.pop_with_type.concrete (st : code.OpIterState)
    (pre : List code.StackType) (expected : types.ValueType)
    (hvals : st.vals.val = pre ++ [.Val expected])
    (hbase : (Control.base st).val ≤ pre.length) :
    code.pop_with_type st expected ⦃ r =>
      r.1 = .Ok (.Val expected) ∧ r.2.vals.val = pre ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨⟨r, st'⟩, hr, hok, hv, hc, hp⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.above_base st pre (.Val expected) hvals hbase)
  dsimp only at hok hv hc hp
  simp [code.pop_with_type, hr, hok, core.result.Result.Insts.CoreOpsTry.branch,
    Translate.valueType_eq, hv, hc, hp]

@[step]
theorem code.pop_with_type.bot (st : code.OpIterState)
    (pre : List code.StackType) (expected : types.ValueType)
    (hvals : st.vals.val = pre ++ [.Bot])
    (hbase : (Control.base st).val ≤ pre.length) :
    code.pop_with_type st expected ⦃ r =>
      r.1 = .Ok .Bot ∧ r.2.vals.val = pre ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨⟨r, st'⟩, hr, hok, hv, hc, hp⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.above_base st pre .Bot hvals hbase)
  dsimp only at hok hv hc hp
  simp [code.pop_with_type, hr, hok, core.result.Result.Insts.CoreOpsTry.branch, hv, hc, hp]

/-- A mismatched concrete operand is consumed before the validator reports the error. -/
theorem code.pop_with_type.mismatch (st : code.OpIterState)
    (pre : List code.StackType) (actual expected : types.ValueType)
    (hvals : st.vals.val = pre ++ [.Val actual])
    (hbase : (Control.base st).val ≤ pre.length) (hne : actual ≠ expected) :
    code.pop_with_type st expected ⦃ r =>
      r.1 = .Err .TypeMismatch ∧ r.2.vals.val = pre ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨⟨r, st'⟩, hr, hok, hv, hc, hp⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.above_base st pre (.Val actual) hvals hbase)
  dsimp only at hok hv hc hp
  have hne' : Translate.valueType actual ≠ Translate.valueType expected :=
    fun h => hne (Translate.valueType_injective h)
  simp [code.pop_with_type, hr, hok, core.result.Result.Insts.CoreOpsTry.branch,
    Translate.valueType_eq, hne', hv, hc, hp]

/-- Popping an expected concrete suffix cannot cross the current frame base. -/
@[step]
theorem code.pop_types_loop.concrete (st : code.OpIterState)
    (ts : Slice types.ValueType) (i : Usize) (pre : List code.StackType)
    (hi : i.val ≤ ts.val.length)
    (hvals : st.vals.val = pre ++ (ts.val.take i.val).map code.StackType.Val)
    (hbase : (Control.base st).val ≤ pre.length) :
    code.pop_types_loop st ts i ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = pre ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  unfold code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ ts.val.length ∧
      p.1.vals.val = pre ++ (ts.val.take p.2.val).map code.StackType.Val ∧
      (Control.base p.1).val ≤ pre.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos)
  · rintro ⟨s, j⟩ ⟨hj, hv, hb, hc, hp⟩
    dsimp only at hj hv hb hc hp
    unfold code.pop_types_loop.body
    dsimp only
    split
    · rename_i hzero
      simp [hzero] at hv
      simp [hv, hc, hp]
    · rename_i hnz
      step
      have hidx : i1.val < ts.val.length := by scalar_tac
      step
      have hv' : s.vals.val =
          (pre ++ (ts.val.take i1.val).map code.StackType.Val) ++ [.Val vt] := by
        rw [hv]
        have hsucc : j.val = i1.val + 1 := by scalar_tac
        rw [hsucc, List.take_succ_eq_append_getElem hidx, List.map_append,
          List.map_singleton, List.append_assoc, vt_post]
      have hb' : (Control.base s).val ≤
          (pre ++ (ts.val.take i1.val).map code.StackType.Val).length := by
        simp only [List.length_append, List.length_map]
        omega
      obtain ⟨⟨res, s'⟩, hpop, hok, hvout, hcout, hpout⟩ :=
        WP.spec_imp_exists (code.pop_with_type.concrete s _ vt hv' hb')
      dsimp only at hok hvout hcout hpout
      rw [hok] at hpop
      rw [WP.spec_equiv_exists]
      refine ⟨.cont (s', i1), ?_, ?_⟩
      · simp [hpop, core.result.Result.Insts.CoreOpsTry.branch]
      dsimp only
      refine ⟨by omega, hvout, ?_, hcout.trans hc, hpout.trans hp, ?_⟩
      · simpa [Control.base, hcout] using hb
      · scalar_tac
  · exact ⟨hi, hvals, hbase, rfl, rfl⟩

@[step]
theorem code.pop_types.concrete (st : code.OpIterState)
    (ts : Slice types.ValueType) (pre : List code.StackType)
    (hvals : st.vals.val = pre ++ ts.val.map code.StackType.Val)
    (hbase : (Control.base st).val ≤ pre.length) :
    code.pop_types st ts ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = pre ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  apply code.pop_types_loop.concrete st ts (Slice.len ts) pre
  · simp
  · simpa using hvals
  · exact hbase

/-- A polymorphic frame base accepts every expected sequence without consuming operands. -/
theorem code.pop_types_loop.polymorphic (st : code.OpIterState)
    (ts : Slice types.ValueType) (i : Usize) (hi : i.val ≤ ts.val.length)
    (hbase : alloc.vec.Vec.len st.vals = Control.base st)
    (hpoly : Control.polymorphic st = true) :
    code.pop_types_loop st ts i = .ok (.Ok (), st) := by
  have hs : code.pop_types_loop st ts i ⦃ r => r = (.Ok (), st) ⦄ := by
    unfold code.pop_types_loop
    apply loop.spec_decr_nat (fun p => p.2.val)
      (fun p => p.1 = st ∧ p.2.val ≤ ts.val.length)
    · rintro ⟨s, j⟩ ⟨hs, hj⟩
      dsimp only at hs hj
      subst s
      unfold code.pop_types_loop.body
      dsimp only
      split
      · simp
      · rename_i hnz
        step
        step
        rw [WP.spec_equiv_exists]
        refine ⟨.cont (st, i1), ?_, ?_⟩
        · simp [code.pop_with_type.polymorphic st vt hbase hpoly,
            core.result.Result.Insts.CoreOpsTry.branch]
        · dsimp only
          exact ⟨rfl, by scalar_tac, by scalar_tac⟩
    · exact ⟨rfl, hi⟩
  obtain ⟨_, h, rfl⟩ := WP.spec_imp_exists hs
  exact h

theorem code.pop_types.polymorphic (st : code.OpIterState)
    (ts : Slice types.ValueType)
    (hbase : alloc.vec.Vec.len st.vals = Control.base st)
    (hpoly : Control.polymorphic st = true) :
    code.pop_types st ts = .ok (.Ok (), st) := by
  exact code.pop_types_loop.polymorphic st ts (Slice.len ts) (by simp) hbase hpoly

/-- The push loop appends its remaining types in source order. -/
@[step]
theorem code.push_types_loop.spec (st : code.OpIterState)
    (ts : Slice types.ValueType) (i : Usize)
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

@[step]
theorem code.push_types.spec (st : code.OpIterState) (ts : Slice types.ValueType)
    (hsize : st.vals.val.length + ts.val.length ≤ Usize.max) :
    code.push_types st ts ⦃ st' =>
      st'.vals.val = st.vals.val ++ ts.val.map code.StackType.Val ∧
      st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  simpa using code.push_types_loop.spec st ts 0#usize (by simp) (by simpa using hsize)

end Itasca
