import Itasca.Wasm2.Simd.Sound
import Itasca.Wasm2.Bulk.Step
import Itasca.Wasm2.Bulk.Dispatch
import Itasca.Wasm2.NumericExt.Sound

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Callbacks may reject, but any successful callback keeps the reader's
independent byte and typing certificate. -/
theorem Pending.reader_run {data env locals index st} (p : Pending data env locals index st)
    {A V : Type} (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V)
    (hr : read ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄)
    (hh : ∀ s a, ∃ reply v', hook v s a = .ok (reply, v')) :
    CoreVisitor.run read hook v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  apply WP.spec_mono (CoreVisitor.run.spec read hook v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ hh)
  · intro r h hok
    exact (h.2 hok).choose_spec
  · apply WP.spec_mono hr
    intro r h
    exact ⟨trivial, fun a ha => h ⟨a, ha⟩⟩

/-- The 0xfc bulk dispatcher transports each independently decoded immediate. -/
theorem Pending.bulk {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hv : FullVisitor.Total visitor)
    (subopcode : U32) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos subopcode next)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) :
    code.step_bulk visitor {st.core with pos := next} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [code.step_bulk.eq_runs]
  unfold bulkStep
  split
  · exact p.reader_run _ _ v (p.memory_init hbyte next hprefix hsize) (fun s a => hv.on_memory_init v s a)
  · exact p.reader_run _ _ v (p.data_drop hbyte next hprefix hsize) (fun s a => hv.on_data_drop v s a)
  · exact p.reader_run _ _ v (p.memory_copy hbyte next hprefix hsize) (fun s _ => hv.on_memory_copy v s)
  · exact p.reader_run _ _ v (p.memory_fill hbyte next hprefix hsize) (fun s _ => hv.on_memory_fill v s)
  · exact p.reader_run _ _ v (p.table_init hbyte next hprefix hsize) (fun s a => hv.on_table_init v s a.1 a.2)
  · exact p.reader_run _ _ v (p.elem_drop hbyte next hprefix hsize) (fun s a => hv.on_elem_drop v s a.1)
  · exact p.reader_run _ _ v (p.table_copy hbyte next hprefix hsize) (fun s a => hv.on_table_copy v s a.1 a.2)
  · exact p.reader_run _ _ v (p.table_grow hbyte next hprefix hsize) (fun s a => hv.on_table_grow v s a)
  · exact p.reader_run _ _ v (p.table_size hbyte next hprefix hsize) (fun s a => hv.on_table_size v s a)
  · exact p.reader_run _ _ v (p.table_fill hbyte next hprefix hsize) (fun s a => hv.on_table_fill v s a)
  · simp

/-- Unified reference, table, bulk and numeric dispatch. SIMD is supplied by
its independently checked branch contract. -/
theorem Pending.wasm2_dispatch {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hv : FullVisitor.Total visitor)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hsimd : data.val[p.start.val]'p.inbounds = 253#u8 →
      code.step_simd visitor st.core data env v ⦃ r =>
        r.1 = .Ok () → p.After {st with core := r.2.1} ⦄) :
    code.step_wasm2 visitor st.core data env ctx opcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  by_cases h253 : opcode = 253#u8
  · rw [h253] at hbyte ⊢
    simpa [code.step_wasm2] using hsimd hbyte
  by_cases h28 : opcode = 28#u8
  · rw [h28] at hbyte ⊢
    rw [code.step_wasm2.typed_select]
    exact p.reader_run _ _ v (p.typed_select hbyte hsize) (fun s a => hv.on_select_typed v s a)
  by_cases h37 : opcode = 37#u8
  · rw [h37] at hbyte ⊢
    rw [code.step_wasm2.table_get]
    exact p.reader_run _ _ v (p.table_get hbyte hsize) (fun s a => hv.on_table_get v s a)
  by_cases h38 : opcode = 38#u8
  · rw [h38] at hbyte ⊢
    rw [code.step_wasm2.table_set]
    exact p.reader_run _ _ v (p.table_set hbyte hsize) (fun s a => hv.on_table_set v s a)
  by_cases h208 : opcode = 208#u8
  · rw [h208] at hbyte ⊢
    rw [code.step_wasm2.ref_null]
    exact p.reader_run _ _ v (p.ref_null hbyte hsize) (fun s a => hv.on_ref_null v s a)
  by_cases h209 : opcode = 209#u8
  · rw [h209] at hbyte ⊢
    rw [code.step_wasm2.ref_is_null]
    exact p.reader_run _ _ v (p.ref_is_null hbyte hsize) (fun s _ => hv.on_ref_is_null v s)
  by_cases h210 : opcode = 210#u8
  · rw [h210] at hbyte ⊢
    rw [code.step_wasm2.ref_func]
    apply p.reader_run _ _ v ?_ (fun s a => hv.on_ref_func v s a)
    apply WP.spec_mono (p.ref_func hbyte hsize)
    rintro r h ⟨idx, hi⟩
    exact (h idx hi).1
  by_cases h252 : opcode = 252#u8
  · rw [h252] at hbyte ⊢
    rw [code.step_wasm2.prefixed]
    obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
    simp only [wasm2PrefixedStep, hr, bind_ok]
    cases r with
    | Err e => simp
    | Ok pair =>
      obtain ⟨subopcode, next⟩ := pair
      dsimp only at *
      split
      · exact p.extended_scalar visitor v hv ctx hlocals 252#u8 (by decide) hsize hbyte
      · exact p.bulk visitor v hv subopcode next hd hsize hbyte
  have hbase : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val := fun he => h (UScalar.eq_of_val_eq he)
    exact ⟨neq h28, neq h37, neq h38, neq h208, neq h209, neq h210, neq h252, neq h253⟩
  rw [code.step_wasm2.base visitor st.core data env ctx opcode v hbase]
  exact p.extended_scalar visitor v hv ctx hlocals opcode hscalar hsize hbyte

/-- Every non-control Core 2.0 instruction preserves the independent body
certificate, including declaration membership for ref.func. -/
theorem Pending.wasm2_scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hv : FullVisitor.Total visitor)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.step_wasm2 visitor st.core data env ctx opcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  exact p.wasm2_dispatch visitor v hv ctx hlocals opcode hscalar hsize hbyte
    (fun hb => p.simd visitor v hv hsize hb)

end Itasca.MultiValue
