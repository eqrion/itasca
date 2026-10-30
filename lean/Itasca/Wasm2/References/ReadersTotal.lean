import Itasca.Wasm2.Scalar.ReadersTotal
import Itasca.Module.Env.References

/-!
# Totality of reference and table readers

`@[step]` lemmas showing that the extracted index, type, table, element, data, bulk-memory,
`ref.*`, table and typed-`select` readers never panic. Each preserves `Control.Shape`, the
control stack and the operand count bound, and moves the cursor forward.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 2000000

namespace Itasca

attribute [local step] code.pop_with_type.total code.pop_stack_type.total
  code.push_val.shape_total Wasm2.ScalarReaders.reserved_zero metadata.Env.declares_function.spec

/-- Index parsing preserves operand capacity as well as frame structure. -/
@[step] theorem code.take_index.total (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) :
    code.take_index st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.take_index.spec st data)
  rintro ⟨r, s⟩ ⟨hv, hc, hd⟩
  dsimp only at hv hc hd ⊢
  refine ⟨⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok idx => exact (Leb128.Decoded.span _ _ _ _ hd).1.le
  | Err e => simp [hd.2]

@[step] theorem code.take_reference_type.total (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) :
    code.take_reference_type st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    simp only [code.take_reference_type, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    conv => arg 1; whnf
    split <;> simp only [WP.spec_ok] <;> exact ⟨⟨hs.ordered, hs.bounded⟩, trivial, by omega, trivial⟩
  · simp [code.take_reference_type, reader.read_byte.eof data st.pos (by omega), hs,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem code.take_value_type.total (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) :
    code.take_value_type st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    simp only [code.take_value_type, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    conv => arg 1; whnf
    split <;> simp only [WP.spec_ok] <;> exact ⟨⟨hs.ordered, hs.bounded⟩, trivial, by omega, trivial⟩
  · simp [code.take_value_type, reader.read_byte.eof data st.pos (by omega), hs,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem code.take_table.total (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (hs : Control.Shape st) :
    code.take_table st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  unfold code.take_table
  step*

@[step] theorem code.take_element.total (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (hs : Control.Shape st) :
    code.take_element st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  unfold code.take_element
  step*

@[step] theorem code.take_data_index.total (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (hs : Control.Shape st) :
    code.take_data_index st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  unfold code.take_data_index
  step*

@[step] theorem code.read_bulk_memory.total (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (hs : Control.Shape st) :
    code.read_bulk_memory st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  unfold code.read_bulk_memory
  simp only [alloc.vec.Vec.is_empty, bind_ok]
  step*

@[step] theorem code.read_bulk_operands.total (st : code.OpIterState) 
    (hs : Control.Shape st) :
    code.read_bulk_operands st  ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 0 ⦄ := by
  unfold code.read_bulk_operands
  step*

@[step] theorem code.read_ref_null.total (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_ref_null st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  unfold code.read_ref_null
  step*

@[step] theorem code.read_ref_is_null.total (st : code.OpIterState) 
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_ref_is_null st  ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  unfold code.read_ref_is_null
  step*

@[step] theorem code.read_ref_func.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_ref_func st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  unfold code.read_ref_func
  step*

@[step] theorem code.read_typed_select.total (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_typed_select st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  unfold code.read_typed_select
  step*

@[step] theorem code.read_table_get.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_table_get st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  unfold code.read_table_get
  step*
  all_goals try (rcases val with ⟨index, ty⟩)
  all_goals step*

@[step] theorem code.read_table_set.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) :
    code.read_table_set st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 0 ⦄ := by
  unfold code.read_table_set
  step*
  all_goals try (rcases val with ⟨index, ty⟩)
  all_goals step*

@[step] theorem code.read_memory_init.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) :
    code.read_memory_init st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 0 ⦄ := by
  unfold code.read_memory_init
  step*

@[step] theorem code.read_memory_copy.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) :
    code.read_memory_copy st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 0 ⦄ := by
  unfold code.read_memory_copy
  step*

@[step] theorem code.read_memory_fill.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) :
    code.read_memory_fill st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 0 ⦄ := by
  unfold code.read_memory_fill
  step*

@[step] theorem code.read_table_init.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) :
    code.read_table_init st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 0 ⦄ := by
  unfold code.read_table_init
  step*
  all_goals try (rcases val with ⟨index, ty⟩)
  all_goals step*
  all_goals try (rcases val1 with ⟨index1, ty1⟩)
  all_goals step*

@[step] theorem code.read_table_copy.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) :
    code.read_table_copy st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 0 ⦄ := by
  unfold code.read_table_copy
  step*
  all_goals try (rcases val with ⟨index, ty⟩)
  all_goals step*
  all_goals try (rcases val1 with ⟨index1, ty1⟩)
  all_goals step*

@[step] theorem code.read_table_grow.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_table_grow st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  unfold code.read_table_grow
  step*
  all_goals try (rcases val with ⟨index, ty⟩)
  all_goals step*

@[step] theorem code.read_table_size.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_table_size st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  unfold code.read_table_size
  step*
  all_goals try (rcases val with ⟨index, ty⟩)
  all_goals step*

@[step] theorem code.read_table_fill.total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Control.Shape st) :
    code.read_table_fill st data env ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length ≤ st.vals.val.length + 0 ⦄ := by
  unfold code.read_table_fill
  step*
  all_goals try (rcases val with ⟨index, ty⟩)
  all_goals step*

end Itasca
