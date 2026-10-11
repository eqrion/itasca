import Itasca.MultiValue.BulkTotal
import Itasca.MultiValue.SimdStepTotal

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Every Core 2.0 opcode is total on a bounded active operand stack when the
visitor hooks return; the cursor never moves backwards. -/
theorem wasm2_total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (hs : Control.Shape st)
    (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes) (hv : FullVisitor.Total visitor) :
    code.step_wasm2 visitor st data env ctx opcode v ⦃ r => Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  by_cases h253 : opcode = 253#u8
  · subst opcode
    apply WP.spec_mono (Simd.simd_total visitor st data env v hs hsize hv)
    rintro r ⟨hshape, hctrl, hpos, _⟩
    exact ⟨hshape, by simp [hctrl], hpos⟩
  by_cases h28 : opcode = 28#u8
  · rw [h28, code.step_wasm2.typed_select]
    apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_typed_select.total st data hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_select_typed v s a
  by_cases h37 : opcode = 37#u8
  · rw [h37, code.step_wasm2.table_get]
    apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_get.total st data env hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_get v s a
  by_cases h38 : opcode = 38#u8
  · rw [h38, code.step_wasm2.table_set]
    apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_set.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_set v s a
  by_cases h208 : opcode = 208#u8
  · rw [h208, code.step_wasm2.ref_null]
    apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_ref_null.total st data hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_ref_null v s a
  by_cases h209 : opcode = 209#u8
  · rw [h209, code.step_wasm2.ref_is_null]
    apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_ref_is_null.total st  hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_ref_is_null v s
  by_cases h210 : opcode = 210#u8
  · rw [h210, code.step_wasm2.ref_func]
    apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_ref_func.total st data env hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_ref_func v s a
  by_cases h252 : opcode = 252#u8
  · rw [h252, code.step_wasm2.prefixed]
    obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
    simp only [wasm2PrefixedStep, hr, bind_ok]
    cases r with
    | Err e => simp [hs]
    | Ok pair =>
      obtain ⟨subopcode, next⟩ := pair
      dsimp only at *
      split
      · exact extended_total visitor st data env ctx 0xfc#u8 v hs hsize (by decide) hv
      · have hp := (Leb128.Decoded.span _ _ _ _ hd).1.le
        apply WP.spec_mono (bulk_total visitor {st with pos := next} data env subopcode v
          ⟨hs.ordered, hs.bounded⟩ hsize hv)
        rintro r ⟨hshape, hctrl, hpos⟩
        exact ⟨hshape, hctrl, hp.trans hpos⟩
  rw [code.step_wasm2.base visitor st data env ctx opcode v (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val := fun he => h (UScalar.eq_of_val_eq he)
    exact ⟨neq h28, neq h37, neq h38, neq h208, neq h209, neq h210, neq h252, neq h253⟩)]
  exact extended_total visitor st data env ctx opcode v hs hsize hscalar hv

end Itasca.MultiValue
