import Itasca.Wasm2.Bulk.Dispatch
import Itasca.Wasm2.References.ReadersTotal
import Itasca.Wasm2.NumericExt.Total

/-!
# Totality of bulk instructions

`bulk_total` shows that `code.step_bulk` never panics under a total visitor, and preserves
`Control.Shape`, the control stack depth and cursor monotonicity for arbitrary immediate bytes.
`run_reader_total` lifts a reader's termination contract through its callback.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A returning hook preserves a reader's structural termination contract. -/
theorem run_reader_total {A V : Type} (st : code.OpIterState)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V)
    (hr : read ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ st.pos.val ≤ r.2.pos.val ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run read hook v ⦃ r => Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  apply WP.spec_mono (CoreVisitor.run.spec read hook v
    (fun s => Control.Shape s ∧ s.ctrls = st.ctrls ∧ st.pos.val ≤ s.pos.val)
    (fun _ _ => True) ?_ hh)
  · rintro r ⟨⟨hs, hc, hp⟩, _⟩
    exact ⟨hs, by simp [hc], hp⟩
  · apply WP.spec_mono hr
    exact fun _ h => ⟨h, by simp⟩

/-- Bulk instructions preserve structural bounds for arbitrary immediate bytes. -/
theorem bulk_total {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hv : FullVisitor.Total visitor) :
    code.step_bulk visitor st data env opcode v ⦃ r => Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  rw [code.step_bulk.eq_runs]
  unfold bulkStep
  split
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_memory_init.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_memory_init v s a
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.take_data_index.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_data_drop v s a
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_memory_copy.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_memory_copy v s
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_memory_fill.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_memory_fill v s
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_init.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_init v s a.1 a.2
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.take_element.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_elem_drop v s a.1
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_copy.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_copy v s a.1 a.2
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_grow.total st data env hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_grow v s a
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_size.total st data env hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_size v s a
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_fill.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_fill v s a
  · simp [hs]

end Itasca.Wasm2
