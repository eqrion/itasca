import Itasca.Wasm2.Step.Dispatch
import Itasca.Wasm2.References.Readers
import Itasca.Wasm2.NumericExt.Total

/-!
Sections, each formerly its own module: Dispatch, Total.
-/

/-! ## Dispatch -/

section

/-!
# Dispatch of bulk instructions

`Wasm2.bulkStep` unfolds the extracted `code.step_bulk` (the `0xFC` subopcodes 8 to 17) into
`CoreVisitor.run` applied to each bulk reader and its visitor callback. `code.step_bulk.eq_runs`
proves the two equal.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Factorization of the bulk instruction callbacks around their readers. -/
def bulkStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) :=
  match opcode with
  | 8#uscalar => CoreVisitor.run (code.read_memory_init st data env) (fun v s a => visitor.on_memory_init v s a) v
  | 9#uscalar => CoreVisitor.run (code.take_data_index st data env) (fun v s a => visitor.on_data_drop v s a) v
  | 10#uscalar => CoreVisitor.run (code.read_memory_copy st data env) (fun v s _ => visitor.on_memory_copy v s) v
  | 11#uscalar => CoreVisitor.run (code.read_memory_fill st data env) (fun v s _ => visitor.on_memory_fill v s) v
  | 12#uscalar => CoreVisitor.run (code.read_table_init st data env) (fun v s a => visitor.on_table_init v s a.1 a.2) v
  | 13#uscalar => CoreVisitor.run (code.take_element st data env) (fun v s a => visitor.on_elem_drop v s a.1) v
  | 14#uscalar => CoreVisitor.run (code.read_table_copy st data env) (fun v s a => visitor.on_table_copy v s a.1 a.2) v
  | 15#uscalar => CoreVisitor.run (code.read_table_grow st data env) (fun v s a => visitor.on_table_grow v s a) v
  | 16#uscalar => CoreVisitor.run (code.read_table_size st data env) (fun v s a => visitor.on_table_size v s a) v
  | 17#uscalar => CoreVisitor.run (code.read_table_fill st data env) (fun v s a => visitor.on_table_fill v s a) v
  | _ => .ok (.Err .UnrecognizedOpcode, st, v)

end Itasca.Wasm2

namespace Itasca

/-- `code.step_bulk` equals its unfolded form `Wasm2.bulkStep`. -/
theorem code.step_bulk.eq_runs {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) :
    code.step_bulk visitor st data env opcode v = Wasm2.bulkStep visitor st data env opcode v := by
  unfold code.step_bulk Wasm2.bulkStep
  split <;> try rfl
  all_goals simp only [CoreVisitor.run]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨r, s⟩ := pair
  all_goals cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  all_goals try (rename_i a; cases (show U32 × U32 from a))
  all_goals try (rename_i a; cases (show U32 × wasm_types.ValueType from a))
  all_goals try simp only [Std.uncurry]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨reply, w⟩ := pair
  all_goals cases reply <;> simp [code.visit]

end Itasca

end

/-! ## Total -/

section

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

end
