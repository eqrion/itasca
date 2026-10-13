import Itasca.Wasm2.Control.Total
import Itasca.Handler.EnvDispatch
import Itasca.Handler.Select
import Itasca.Handler.ScalarConst

/-!
# Totality of the scalar readers

Totality of the extracted `code.take_*` and `code.read_*` helpers used by the shared scalar
`code.step` arms (locals, globals, memory, constants, `drop` and `select`). Each lemma in
`Wasm2.ScalarReaders` shows that the reader terminates, preserves `Control.Shape` and never moves
the cursor back, on arbitrary bytes and environments.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Pushing a value preserves frame bounds for arbitrary frames. -/
theorem code.push_val.shape_total (st : code.OpIterState) (t : code.StackType)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.push_val st t ⦃ s => Control.Shape s ∧ s.ctrls = st.ctrls ∧ s.pos = st.pos ∧
      s.vals.val.length = st.vals.val.length + 1 ⦄ := by
  apply WP.spec_mono (code.push_val.spec st t hsize)
  rintro s ⟨hv, hc, hp⟩
  exact ⟨hs.replace_operands hc (by simp [hv]; have := hs.base_le; omega),
    hc, hp, by simp [hv]⟩

namespace Wasm2.ScalarReaders

private theorem same_stacks {st s : code.OpIterState} (hs : Control.Shape st)
    (hc : s.ctrls = st.ctrls) (hv : s.vals = st.vals) : Control.Shape s :=
  ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩

theorem take_local (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (hs : Control.Shape st) :
    code.take_local st data ctx ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.take_local.spec st data ctx)
  rintro ⟨r, s⟩ ⟨hv, hc, hp⟩
  dsimp only at hv hc hp ⊢
  refine ⟨same_stacks hs hc hv, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok pair => exact (Leb128.Decoded.span _ _ _ _ hp.1).1.le
  | Err e =>
    rcases hp with ⟨_, hp⟩ | ⟨_, idx, hd, _⟩
    · simp [hp]
    · exact (Leb128.Decoded.span _ _ _ _ hd).1.le

theorem take_global (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (hs : Control.Shape st) :
    code.take_global st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.take_global.spec st data env)
  rintro ⟨r, s⟩ ⟨hv, hc, hp⟩
  dsimp only at hv hc hp ⊢
  refine ⟨same_stacks hs hc hv, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok pair => exact (Leb128.Decoded.span _ _ _ _ hp.1).1.le
  | Err e =>
    rcases hp with ⟨_, hp⟩ | ⟨_, idx, hd, _⟩
    · simp [hp]
    · exact (Leb128.Decoded.span _ _ _ _ hd).1.le

theorem reserved_zero (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) :
    code.read_reserved_zero st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.read_reserved_zero.spec st data)
  rintro ⟨r, s⟩ ⟨hv, hc, hp⟩
  dsimp only at hv hc hp ⊢
  refine ⟨same_stacks hs hc hv, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok u => obtain ⟨_, _, hp⟩ := hp; omega
  | Err e => simp [hp.1]

theorem memarg (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) :
    code.read_memarg st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.read_memarg.spec st data)
  rintro ⟨r, s⟩ ⟨hv, hc, hp⟩
  dsimp only at hv hc hp ⊢
  refine ⟨same_stacks hs hc hv, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok arg =>
    obtain ⟨middle, h1, h2⟩ := hp
    exact le_trans (Leb128.Decoded.span _ _ _ _ h1).1.le
      (Leb128.Decoded.span _ _ _ _ h2).1.le
  | Err e => simp [hp.1]

attribute [local step] take_local take_global reserved_zero memarg
  code.pop_with_type.total code.pop_stack_type.total code.push_val.shape_total
  code.require_memory.spec code.check_memory_and_alignment.spec code.join_stack_type.spec

theorem local_get (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_local_get st data ctx ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_local_get
  step*
  cases val
  step*

theorem local_set (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (hs : Control.Shape st) (_hsize : st.vals.val.length < Usize.max) :
    code.read_local_set st data ctx ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_local_set
  step*
  cases val
  step*

theorem local_tee (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_local_tee st data ctx ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_local_tee
  step*
  cases val
  step*

theorem global_get (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_global_get st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_global_get
  step*
  cases val
  step*

theorem global_set (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (hs : Control.Shape st) (_hsize : st.vals.val.length < Usize.max) :
    code.read_global_set st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_global_set
  step*
  cases val
  step*

theorem memory_size (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_memory_size st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_memory_size
  step*

theorem memory_grow (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_memory_grow st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_memory_grow
  step*

theorem load (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ty : types.ValueType) (align : U32)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_load st data env ty align ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_load
  step*

theorem store (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ty : types.ValueType) (align : U32)
    (hs : Control.Shape st) (_hsize : st.vals.val.length < Usize.max) :
    code.read_store st data env ty align ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_store
  step*

@[local step] private theorem select_type_total (t : code.StackType) :
    code.is_select_type t ⦃ _ => True ⦄ := by simp

theorem select (st : code.OpIterState) 
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_select st  ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_select
  step*

theorem drop (st : code.OpIterState) 
    (hs : Control.Shape st) (_hsize : st.vals.val.length < Usize.max) :
    code.read_drop st  ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_drop
  step*

theorem i32_const (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_i32_const st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  apply WP.spec_mono (code.read_i32_const.spec st data hsize)
  rintro ⟨r, s⟩ ⟨hc, hp⟩
  dsimp only at hc hp ⊢
  cases r with
  | Err e => simpa [hp.2] using (show Control.Shape st ∧ st.ctrls = st.ctrls ∧ st.pos.val ≤ st.pos.val from ⟨hs, rfl, le_refl _⟩)
  | Ok value =>
    obtain ⟨hd, hv⟩ := hp
    refine ⟨hs.replace_operands hc ?_, hc, (SignedLeb32.Decoded.span _ _ _ _ hd).1.le⟩
    simp only [hv, List.length_append, List.length_singleton]
    have := hs.base_le
    omega

theorem i64_const (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_i64_const st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  apply WP.spec_mono (code.read_i64_const.spec st data hsize)
  rintro ⟨r, s⟩ ⟨hc, hp⟩
  dsimp only at hc hp ⊢
  cases r with
  | Err e => simpa [hp.2] using (show Control.Shape st ∧ st.ctrls = st.ctrls ∧ st.pos.val ≤ st.pos.val from ⟨hs, rfl, le_refl _⟩)
  | Ok value =>
    obtain ⟨hd, hv⟩ := hp
    refine ⟨hs.replace_operands hc ?_, hc, (SignedLeb64.Decoded.span _ _ _ _ hd).1.le⟩
    simp only [hv, List.length_append, List.length_singleton]
    have := hs.base_le
    omega

theorem f32_const (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_f32_const st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  apply WP.spec_mono (code.read_f32_const.spec st data hsize)
  rintro ⟨r, s⟩ ⟨hc, hp⟩
  dsimp only at hc hp ⊢
  cases r with
  | Err e => simpa [hp.2] using (show Control.Shape st ∧ st.ctrls = st.ctrls ∧ st.pos.val ≤ st.pos.val from ⟨hs, rfl, le_refl _⟩)
  | Ok value =>
    obtain ⟨hd, hv⟩ := hp
    refine ⟨hs.replace_operands hc ?_, hc, by have := (FloatBits.Decoded.span _ _ _ _ _ hd).1; omega⟩
    simp only [hv, List.length_append, List.length_singleton]
    have := hs.base_le
    omega

theorem f64_const (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_f64_const st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  apply WP.spec_mono (code.read_f64_const.spec st data hsize)
  rintro ⟨r, s⟩ ⟨hc, hp⟩
  dsimp only at hc hp ⊢
  cases r with
  | Err e => simpa [hp.2] using (show Control.Shape st ∧ st.ctrls = st.ctrls ∧ st.pos.val ≤ st.pos.val from ⟨hs, rfl, le_refl _⟩)
  | Ok value =>
    obtain ⟨hd, hv⟩ := hp
    refine ⟨hs.replace_operands hc ?_, hc, by have := (FloatBits.Decoded.span _ _ _ _ _ hd).1; omega⟩
    simp only [hv, List.length_append, List.length_singleton]
    have := hs.base_le
    omega

end Wasm2.ScalarReaders
end Itasca
