import Itasca.Handler.Branch
import Itasca.Handler.Stack

/-!
# End and else handlers

Case-by-case specifications of the extracted `code.read_end` and `code.read_else`: empty frames,
concrete results, unreachable frames and the rejected cases (`StackMismatch`). The `*_context`
theorems add that `Control.Shape` is preserved and the label context drops the closed frame.
`code.block_loop_empty_roundtrip` closes a nested empty `block` and `loop`.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Pushing no types leaves the state unchanged. -/
theorem code.push_types.empty (st : code.OpIterState) (ts : Slice types.ValueType)
    (h : ts.val = []) : code.push_types st ts = .ok st := by
  have hn : Slice.len ts = 0#usize := by scalar_tac
  unfold code.push_types code.push_types_loop
  rw [loop]
  simp [code.push_types_loop.body, hn]

/-- `code.read_end` with no control frame returns `StackMismatch`. -/
theorem code.read_end.no_frame (st : code.OpIterState) (h : st.ctrls.val = []) :
    code.read_end st = .ok (.Err .StackMismatch, st) := by
  have hn : alloc.vec.Vec.len st.ctrls = 0#usize := by scalar_tac
  simp [code.read_end, hn]

private theorem read_end_finish (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (rs : alloc.vec.Vec types.ValueType) (popped : code.OpIterState)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hresults : code.block_results c.block_type = .ok rs)
    (hthen : c.kind = .Then → rs.val = [])
    (hpop : code.pop_types st (alloc.vec.Vec.deref rs) = .ok (.Ok (), popped))
    (hbase : popped.vals.val.length = c.value_stack_base.val)
    (hpc : popped.ctrls = st.ctrls) (hpos : popped.pos = st.pos)
    (hsize : popped.vals.val.length + rs.val.length ≤ Usize.max) :
    code.read_end st ⦃ r =>
      r.1 = .Ok (c.kind, c.block_type) ∧ r.2.ctrls.val = cs ∧
      r.2.vals.val = popped.vals.val ++ rs.val.map code.StackType.Val ∧
      r.2.pos = st.pos ⦄ := by
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  unfold code.read_end
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq, hresults]
  simp only [bind_ok]
  cases hk : c.kind <;>
    simp [code.is_then, alloc.vec.Vec.is_empty, hthen, hk, hpop,
      core.result.Result.Insts.CoreOpsTry.branch, hbase]
  all_goals
    step*
  all_goals simp_all [alloc.vec.Vec.deref]

/-- `code.read_end` on a frame with an empty block type and no operands above its base pops the
frame and leaves the operands unchanged, including for an `if` with no `else`. -/
@[step]
theorem code.read_end.empty (st : code.OpIterState) (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c]) (hbt : c.block_type = .Empty)
    (hbase : st.vals.val.length = c.value_stack_base.val) :
    code.read_end st ⦃ r =>
      r.1 = .Ok (c.kind, .Empty) ∧ r.2.ctrls.val = cs ∧
      r.2.vals = st.vals ∧ r.2.pos = st.pos ⦄ := by
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  have hpop := code.pop_types.empty st (alloc.vec.Vec.deref (alloc.vec.Vec.new types.ValueType)) rfl
  have hpush (s : code.OpIterState) := code.push_types.empty s
    (alloc.vec.Vec.deref (alloc.vec.Vec.new types.ValueType)) rfl
  unfold code.read_end
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq]
  simp only [hbt, code.block_results, bind_ok]
  cases hk : c.kind <;>
    simp [code.is_then, alloc.vec.Vec.is_empty, hpop,
      core.result.Result.Insts.CoreOpsTry.branch, hbase, alloc.vec.Vec.pop,
      hpush, hctrls]

/-- `code.read_end` with matching concrete results on top of the operands leaves them in place and
removes only the innermost frame. -/
@[step]
theorem code.read_end.concrete (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (pre : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hvals : st.vals.val = pre ++ (Control.results c.block_type).map code.StackType.Val)
    (hbase : pre.length = c.value_stack_base.val)
    (hthen : c.kind = .Then → c.block_type = .Empty) :
    code.read_end st ⦃ r =>
      r.1 = .Ok (c.kind, c.block_type) ∧ r.2.ctrls.val = cs ∧
      r.2.vals = st.vals ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.block_results.spec c.block_type)
  obtain ⟨⟨_, popped⟩, hpop, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.pop_types.concrete st (alloc.vec.Vec.deref rs) pre
      (by simpa [alloc.vec.Vec.deref, hrsv] using hvals)
      (by simp [Control.base, hctrls, hbase]))
  dsimp only at hv hc hp
  have hsize : popped.vals.val.length + rs.val.length ≤ Usize.max := by
    have hs := st.vals.property
    simpa [hvals, hv, hrsv] using hs
  obtain ⟨⟨r, st'⟩, hr, hok, hcs, hvs, hps⟩ := WP.spec_imp_exists
    (read_end_finish st cs c rs popped hctrls hrs
      (by intro hk; simp [hrsv, hthen hk, Control.results]) hpop
      (by rw [hv, hbase]) hc hp hsize)
  dsimp only at hok hcs hvs hps
  rw [hr]
  simp only [WP.spec_ok]
  exact ⟨hok, hcs, alloc.vec.Vec.ext _ _ (by rw [hvs, hv, hrsv, ← hvals]), hps⟩

/-- `code.read_end` on a polymorphic frame with no operands pushes the block's results as concrete
types after removing the frame. -/
@[step]
theorem code.read_end.polymorphic (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (hctrls : st.ctrls.val = cs ++ [c])
    (hbase : st.vals.val.length = c.value_stack_base.val)
    (hpoly : c.polymorphic_base = true)
    (hthen : c.kind = .Then → c.block_type = .Empty)
    (hsize : st.vals.val.length + (Control.results c.block_type).length ≤ Usize.max) :
    code.read_end st ⦃ r =>
      r.1 = .Ok (c.kind, c.block_type) ∧ r.2.ctrls.val = cs ∧
      r.2.vals.val = st.vals.val ++ (Control.results c.block_type).map code.StackType.Val ∧
      r.2.pos = st.pos ⦄ := by
  obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.block_results.spec c.block_type)
  have hpop := code.pop_types.polymorphic st (alloc.vec.Vec.deref rs)
    (by apply UScalar.eq_of_val_eq; simpa [Control.base, hctrls] using hbase)
    (by simp [Control.polymorphic, hctrls, hpoly])
  simpa [hrsv] using read_end_finish st cs c rs st hctrls hrs
    (by intro hk; simp [hrsv, hthen hk, Control.results]) hpop hbase rfl rfl
    (by simpa [hrsv] using hsize)

/-- `code.read_end` on an empty block type returns `StackMismatch` when operands remain above the
frame base, even after an unreachable instruction. -/
@[step]
theorem code.read_end.empty_mismatch (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (hctrls : st.ctrls.val = cs ++ [c])
    (hbt : c.block_type = .Empty) (hbase : st.vals.val.length ≠ c.value_stack_base.val) :
    code.read_end st ⦃ r => r = (.Err .StackMismatch, st) ⦄ := by
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  have hpop := code.pop_types.empty st (alloc.vec.Vec.deref (alloc.vec.Vec.new types.ValueType)) rfl
  unfold code.read_end
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq]
  simp only [hbt, code.block_results, bind_ok]
  cases hk : c.kind <;>
    simp [code.is_then, alloc.vec.Vec.is_empty, hpop,
      core.result.Result.Insts.CoreOpsTry.branch, hbase]

/-- `code.read_end` on a `Then` frame with a result returns `StackMismatch`, since Wasm 1.0 forbids
a result on an `if` with no `else`. -/
@[step]
theorem code.read_end.then_result (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (t : types.ValueType) (hctrls : st.ctrls.val = cs ++ [c])
    (hkind : c.kind = .Then) (hbt : c.block_type = .Value t) :
    code.read_end st ⦃ r => r = (.Err .StackMismatch, st) ⦄ := by
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  unfold code.read_end
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq]
  step
  simp [code.is_then, hkind, alloc.vec.Vec.is_empty, results_post, hbt, Control.results]

/-- `code.read_else` on an empty `Then` frame turns it into an `Else` frame and resets its
polymorphism. -/
@[step]
theorem code.read_else.empty (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (hctrls : st.ctrls.val = cs ++ [c])
    (hkind : c.kind = .Then) (hbt : c.block_type = .Empty)
    (hbase : st.vals.val.length = c.value_stack_base.val) :
    code.read_else st ⦃ r =>
      r.1 = .Ok .Empty ∧
      r.2.ctrls.val = cs ++ [{ c with kind := .Else, polymorphic_base := false }] ∧
      r.2.vals = st.vals ∧ r.2.pos = st.pos ⦄ := by
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  have hpop := code.pop_types.empty st (alloc.vec.Vec.deref (alloc.vec.Vec.new types.ValueType)) rfl
  unfold code.read_else
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq]
  simp [code.is_then, hkind, hbt, code.block_results,
    hpop, core.result.Result.Insts.CoreOpsTry.branch]
  have hi : i.val = cs.length := by
    simpa [hctrls] using i_post
  step*
  all_goals simp_all [alloc.vec.Vec.set]

namespace Control

/-- Popping a frame preserves `Shape` when the operands cover the popped frame's base. -/
theorem Shape.exit {st st' : code.OpIterState} (h : Shape st)
    (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c]) (hctrls' : st'.ctrls.val = cs)
    (hbase : c.value_stack_base.val ≤ st'.vals.val.length) : Shape st' := by
  have hord := h.ordered
  rw [hctrls, List.pairwise_append] at hord
  constructor
  · simpa [hctrls'] using hord.1
  · intro d hd
    rw [hctrls'] at hd
    exact Nat.le_trans (hord.2.2 d hd c (by simp)) hbase

/-- Popping a frame removes the innermost label. -/
theorem labels_exit (st st' : code.OpIterState) (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c]) (hctrls' : st'.ctrls.val = cs) :
    (labels st.ctrls.val).tail = labels st'.ctrls.val := by
  simp [hctrls, hctrls', labels_push]

end Control

/-- `code.read_end.empty` also preserves `Control.Shape` and drops the innermost label. -/
theorem code.read_end.empty_context (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (hshape : Control.Shape st) (hctrls : st.ctrls.val = cs ++ [c])
    (hbt : c.block_type = .Empty) (hbase : st.vals.val.length = c.value_stack_base.val) :
    ∃ st', code.read_end st = .ok (.Ok (c.kind, .Empty), st') ∧
      st'.ctrls.val = cs ∧ st'.vals = st.vals ∧ st'.pos = st.pos ∧
      Control.Shape st' ∧ (Control.labels st.ctrls.val).tail = Control.labels st'.ctrls.val := by
  obtain ⟨⟨_, st'⟩, hr, rfl, hc, hv, hp⟩ :=
    WP.spec_imp_exists (code.read_end.empty st cs c hctrls hbt hbase)
  exact ⟨st', hr, hc, hv, hp,
    Control.Shape.exit hshape cs c hctrls hc (by rw [hv, hbase]),
    Control.labels_exit st st' cs c hctrls hc⟩

/-- `code.read_end.concrete` also preserves `Control.Shape` and drops the innermost label. -/
theorem code.read_end.concrete_context (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (pre : List code.StackType) (hshape : Control.Shape st)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hvals : st.vals.val = pre ++ (Control.results c.block_type).map code.StackType.Val)
    (hbase : pre.length = c.value_stack_base.val)
    (hthen : c.kind = .Then → c.block_type = .Empty) :
    ∃ st', code.read_end st = .ok (.Ok (c.kind, c.block_type), st') ∧
      st'.ctrls.val = cs ∧ st'.vals = st.vals ∧ st'.pos = st.pos ∧
      Control.Shape st' ∧ (Control.labels st.ctrls.val).tail = Control.labels st'.ctrls.val := by
  obtain ⟨⟨_, st'⟩, hr, rfl, hc, hv, hp⟩ :=
    WP.spec_imp_exists (code.read_end.concrete st cs c pre hctrls hvals hbase hthen)
  dsimp only at hc hv hp
  refine ⟨st', hr, hc, hv, hp, ?_, Control.labels_exit st st' cs c hctrls hc⟩
  apply Control.Shape.exit hshape cs c hctrls hc
  rw [hv, hvals, List.length_append, List.length_map, hbase]
  omega

/-- `code.read_end.polymorphic` also preserves `Control.Shape` and drops the innermost label. -/
theorem code.read_end.polymorphic_context (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (hshape : Control.Shape st) (hctrls : st.ctrls.val = cs ++ [c])
    (hbase : st.vals.val.length = c.value_stack_base.val) (hpoly : c.polymorphic_base = true)
    (hthen : c.kind = .Then → c.block_type = .Empty)
    (hsize : st.vals.val.length + (Control.results c.block_type).length ≤ Usize.max) :
    ∃ st', code.read_end st = .ok (.Ok (c.kind, c.block_type), st') ∧
      st'.ctrls.val = cs ∧
      st'.vals.val = st.vals.val ++ (Control.results c.block_type).map code.StackType.Val ∧
      st'.pos = st.pos ∧ Control.Shape st' ∧
      (Control.labels st.ctrls.val).tail = Control.labels st'.ctrls.val := by
  obtain ⟨⟨_, st'⟩, hr, rfl, hc, hv, hp⟩ :=
    WP.spec_imp_exists (code.read_end.polymorphic st cs c hctrls hbase hpoly hthen hsize)
  dsimp only at hc hv hp
  refine ⟨st', hr, hc, hv, hp, ?_, Control.labels_exit st st' cs c hctrls hc⟩
  apply Control.Shape.exit hshape cs c hctrls hc
  rw [hv, List.length_append, List.length_map, hbase]
  omega

/-- Reading an empty `block` then an empty `loop`, and ending both, restores the original stacks
and advances the position by two bytes. -/
theorem code.block_loop_empty_roundtrip (st : code.OpIterState) (data : Slice U8)
    (hshape : Control.Shape st) (hdata : st.pos.val + 1 < data.val.length)
    (hblock : data.val[st.pos.val]'(by omega) = 64#u8)
    (hloop : data.val[st.pos.val + 1]'hdata = 64#u8)
    (hsize : st.ctrls.val.length + 2 ≤ Usize.max) :
    ∃ s₁ s₂ s₃ s₄,
      code.read_block st data = .ok (.Ok .Empty, s₁) ∧
      code.read_loop s₁ data = .ok (.Ok .Empty, s₂) ∧
      code.read_end s₂ = .ok (.Ok (.Loop, .Empty), s₃) ∧
      code.read_end s₃ = .ok (.Ok (.Block, .Empty), s₄) ∧
      s₄.vals = st.vals ∧ s₄.ctrls = st.ctrls ∧ s₄.pos.val = st.pos.val + 2 ∧
      Control.Shape s₄ := by
  obtain ⟨⟨_, s₁⟩, hr₁, rfl, hp₁, hv₁, hc₁⟩ := WP.spec_imp_exists
    (code.read_block.spec st data .Empty (by exact Nat.lt_of_succ_lt hdata) hblock (by omega) trivial)
  dsimp only at hp₁ hv₁ hc₁
  have hs₁ := Control.Shape.push hshape .Block .Empty hc₁ hv₁
  obtain ⟨⟨_, s₂⟩, hr₂, rfl, hp₂, hv₂, hc₂⟩ := WP.spec_imp_exists
    (code.read_loop.spec s₁ data .Empty (by simpa [hp₁] using hdata)
      (by simpa [Control.blockByte, hp₁] using hloop) (by simp [hc₁]; omega) trivial)
  dsimp only at hp₂ hv₂ hc₂
  have hs₂ := Control.Shape.push hs₁ .Loop .Empty hc₂ hv₂
  obtain ⟨s₃, hr₃, hc₃, hv₃, hp₃, hs₃, _⟩ :=
    code.read_end.empty_context s₂ s₁.ctrls.val (Control.frame s₁ .Loop .Empty)
      hs₂ hc₂ rfl (by simp [Control.frame, hv₂])
  have hc₃' : s₃.ctrls.val = st.ctrls.val ++ [Control.frame st .Block .Empty] := by
    rw [hc₃, hc₁]
  obtain ⟨s₄, hr₄, hc₄, hv₄, hp₄, hs₄, _⟩ :=
    code.read_end.empty_context s₃ st.ctrls.val (Control.frame st .Block .Empty)
      hs₃ hc₃' rfl (by simp [Control.frame, hv₃, hv₂, hv₁])
  refine ⟨s₁, s₂, s₃, s₄, hr₁, hr₂, hr₃, hr₄, ?_, ?_, ?_, hs₄⟩
  · rw [hv₄, hv₃, hv₂, hv₁]
  · exact alloc.vec.Vec.ext _ _ hc₄
  · rw [hp₄, hp₃]
    omega

end Itasca
