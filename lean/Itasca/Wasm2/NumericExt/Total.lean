import Itasca.Wasm2.NumericExt.Dispatch
import Itasca.Wasm2.Scalar.Total

open Aeneas Aeneas.Std

namespace Itasca.FullVisitor

theorem Total.visit_sign_extension {V : Type} {visitor : code.OpVisitor V}
    (h : Total visitor) (v : V) (st : code.OpIterState) (opcode : U8) :
    ∃ res v', code.visit_sign_extension visitor v st opcode = .ok (res, v') := by
  unfold code.visit_sign_extension
  split
  · exact h.on_i32_extend8_s v st
  · exact h.on_i32_extend16_s v st
  · exact h.on_i64_extend8_s v st
  · exact h.on_i64_extend16_s v st
  · exact h.on_i64_extend32_s v st
  · exact ⟨.Ok (), v, rfl⟩

theorem Total.visit_saturating {V : Type} {visitor : code.OpVisitor V}
    (h : Total visitor) (v : V) (st : code.OpIterState) (opcode : U32) :
    ∃ res v', code.visit_saturating visitor v st opcode = .ok (res, v') := by
  unfold code.visit_saturating
  split
  · exact h.on_i32_trunc_sat_f32_s v st
  · exact h.on_i32_trunc_sat_f32_u v st
  · exact h.on_i32_trunc_sat_f64_s v st
  · exact h.on_i32_trunc_sat_f64_u v st
  · exact h.on_i64_trunc_sat_f32_s v st
  · exact h.on_i64_trunc_sat_f32_u v st
  · exact h.on_i64_trunc_sat_f64_s v st
  · exact h.on_i64_trunc_sat_f64_u v st
  · exact ⟨.Ok (), v, rfl⟩

theorem Accepts.visit_sign_extension {V : Type} {visitor : code.OpVisitor V}
    (h : Accepts visitor) (v : V) (st : code.OpIterState) (opcode : U8) :
    ∃ v', code.visit_sign_extension visitor v st opcode = .ok (.Ok (), v') := by
  unfold code.visit_sign_extension
  split
  · exact h.on_i32_extend8_s v st
  · exact h.on_i32_extend16_s v st
  · exact h.on_i64_extend8_s v st
  · exact h.on_i64_extend16_s v st
  · exact h.on_i64_extend32_s v st
  · exact ⟨v, rfl⟩

theorem Accepts.visit_saturating {V : Type} {visitor : code.OpVisitor V}
    (h : Accepts visitor) (v : V) (st : code.OpIterState) (opcode : U32) :
    ∃ v', code.visit_saturating visitor v st opcode = .ok (.Ok (), v') := by
  unfold code.visit_saturating
  split
  · exact h.on_i32_trunc_sat_f32_s v st
  · exact h.on_i32_trunc_sat_f32_u v st
  · exact h.on_i32_trunc_sat_f64_s v st
  · exact h.on_i32_trunc_sat_f64_u v st
  · exact h.on_i64_trunc_sat_f32_s v st
  · exact h.on_i64_trunc_sat_f32_u v st
  · exact h.on_i64_trunc_sat_f64_s v st
  · exact h.on_i64_trunc_sat_f64_u v st
  · exact ⟨v, rfl⟩

end Itasca.FullVisitor

namespace Itasca.MultiValue

private theorem conversion_total (st : code.OpIterState) (input output : types.ValueType)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r => Control.Shape r.2 ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  let n := (Control.base st).val
  have hn : n ≤ st.vals.val.length := hs.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, after, hv, _, _⟩ := WP.spec_imp_exists
    (code.read_conversion.segment st (st.vals.val.take n) (st.vals.val.drop n) input output
      (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]) hsize)
  rw [hr, WP.spec_ok]
  refine ⟨hs.replace_operands hc ?_, hc, hp⟩
  simp [hv, n, Nat.min_eq_left hn]

private theorem conversion_run_total {V : Type} (st : code.OpIterState)
    (input output : types.ValueType)
    (hook : V → code.OpIterState → Unit → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run (code.read_conversion st input output) hook v ⦃ r =>
      Control.Shape r.2.1 ∧ r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ⦄ := by
  apply WP.spec_mono (CoreVisitor.run.spec _ _ v
    (fun s => Control.Shape s ∧ s.ctrls = st.ctrls ∧ s.pos = st.pos) (fun _ _ => True) ?_ hh)
  · intro r h
    exact h.1
  · apply WP.spec_mono (conversion_total st input output hs hsize)
    exact fun _ h => ⟨h, by simp⟩

/-- Added numeric instructions terminate with ordinary returning hooks. -/
theorem extended_total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (hs : Control.Shape st)
    (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes) (hv : FullVisitor.Total visitor) :
    code.step_extended visitor st data env ctx opcode v ⦃ r => Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some op =>
    rw [code.step_extended.sign visitor st data env ctx opcode op v hm]
    apply WP.spec_mono (conversion_run_total st op.input op.output _ v hs hsize
      (fun s _ => hv.visit_sign_extension v s opcode))
    rintro r ⟨hh, hc, hp⟩
    exact ⟨hh, by simp [hc], by simp [hp]⟩
  | none =>
    by_cases hp : opcode = code.OP_MISC_PREFIX
    · have he : opcode = 0xFC#u8 := by simpa [global_simps] using hp
      rw [he]
      rw [code.step_extended.prefixed]
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
      unfold prefixedStep
      rw [hr]
      simp only [bind_ok]
      cases r with
      | Err e => simp [hs]
      | Ok pair =>
        obtain ⟨subopcode, next⟩ := pair
        have hspan := Leb128.Decoded.span data st.pos subopcode next hd
        cases hm : NumericExtensions.saturatingMeaning subopcode with
        | none =>
          simp only [hm, WP.spec_ok]
          exact ⟨⟨hs.ordered, hs.bounded⟩, trivial, Nat.le_of_lt hspan.1⟩
        | some op =>
          simp only [hm]
          apply WP.spec_mono (conversion_run_total {st with pos := next} op.input op.output _ v
            ⟨hs.ordered, hs.bounded⟩ hsize (fun s _ => hv.visit_saturating v s subopcode))
          rintro r ⟨hh, hc, hp⟩
          exact ⟨hh, by simpa [hc], by simpa [hp] using Nat.le_of_lt hspan.1⟩
    · rw [code.step_extended.base visitor st data env ctx opcode v hm hp]
      exact scalar_total visitor st data env ctx opcode v hs hsize hscalar hv

end Itasca.MultiValue
