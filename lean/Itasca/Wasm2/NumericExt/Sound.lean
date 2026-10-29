import Itasca.Wasm2.Scalar.NumericReader
import Itasca.Wasm2.Scalar.Step
import Itasca.Wasm2.NumericExt.Total

/-!
# Numeric extension steps

`Pending` preservation for `code.step_extended`. `Pending.extended_numeric` handles a unary
numeric extension, and `Pending.extended_scalar` combines the sign-extension, saturating and
shared-scalar arms into one successful-step certificate.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A unary numeric extension preserves the control zipper while recording
its independently encoded instruction, including any consumed prefix bytes. -/
theorem Pending.extended_numeric {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (v : V)
    (operation : Numeric.Operation) (hunary : operation.binary = false)
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) operation.instruction)
    (pos : Usize) (hsize : st.core.vals.val.length < Usize.max)
    (hook : V → code.OpIterState → Unit → Result (core.result.Result Unit error.VisitError × V))
    (hhook : ∀ s a, ∃ reply v', hook v s a = .ok (reply, v'))
    (hencoded : At data p.start (.plain operation.instruction) pos)
    (hwasm2 : profile ≠ .Wasm1) :
    CoreVisitor.run (code.read_conversion {st.core with pos := pos} operation.input operation.output)
      hook v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  have effect := p.numeric_reader operation pos hsize hencoded hdecl
    (fun hp => absurd hp hwasm2)
  simp only [Numeric.read, hunary, Bool.false_eq_true, ↓reduceIte] at effect
  apply WP.spec_mono (CoreVisitor.run.spec _ hook v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ hhook)
  · intro r hr accepted
    exact (hr.2 accepted).choose_spec
  · apply WP.spec_mono effect
    intro r hr
    refine ⟨trivial, ?_⟩
    intro unit accepted
    obtain ⟨_, _, post⟩ := hr.2.2 unit accepted
    exact post.after

/-- Scalar extensions and the base dispatcher share the same successful-step certificate. -/
theorem Pending.extended_scalar {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hv : FullVisitor.Total visitor)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.step_extended visitor st.core data env ctx opcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some operation =>
    rw [code.step_extended.sign visitor st.core data env ctx opcode operation v hm]
    apply p.extended_numeric (hwasm2 := p.not_wasm1 hbyte (Wasm1.signMeaning_extension hm)) v
      operation (NumericExtensions.sign_properties hm).1 (NumericExtensions.sign_declared hm _) st.core.pos hsize
      _ (fun s _ => hv.visit_sign_extension v s opcode)
    exact At.of_immediate p.inbounds hbyte p.pos (.signExtension opcode operation hm)
      (Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega))
  | none =>
    by_cases hprefix : opcode = code.OP_MISC_PREFIX
    · have he : opcode = 0xFC#u8 := by simpa [global_simps] using hprefix
      rw [he] at hbyte ⊢
      rw [code.step_extended.prefixed]
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
      unfold prefixedStep
      rw [hr]
      simp only [bind_ok]
      cases r with
      | Err e => simp
      | Ok pair =>
        obtain ⟨subopcode, next⟩ := pair
        cases hm : NumericExtensions.saturatingMeaning subopcode with
        | none => simp [hm]
        | some operation =>
          simp only [hm]
          apply p.extended_numeric (hwasm2 := p.not_wasm1 hbyte (by decide)) v
            operation (NumericExtensions.saturating_unary hm) (NumericExtensions.saturating_declared hm _) next hsize
            _ (fun s _ => hv.visit_saturating v s subopcode)
          obtain ⟨bytes, hs, hn, hb, he⟩ := hd
          exact At.of_immediate p.inbounds hbyte p.pos (.saturating subopcode operation hm he)
            ⟨hs, hn, hb⟩
    · rw [code.step_extended.base visitor st.core data env ctx opcode v hm hprefix]
      exact p.scalar visitor v hv ctx hlocals opcode hscalar hsize hbyte

end Itasca.Wasm2
