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
theorem Pending.extended_numeric {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (v : V)
    (operation : Numeric.Operation) (hunary : operation.binary = false)
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) operation.instruction)
    (pos : Usize) (hsize : st.core.vals.val.length < Usize.max)
    (hook : V → code.OpIterState → Unit → Result (core.result.Result Unit error.VisitError × V))
    (hhook : ∀ s a, ∃ reply v', hook v s a = .ok (reply, v'))
    (hencoded : At data p.start (.plain operation.instruction) pos) :
    CoreVisitor.run (code.read_conversion {st.core with pos := pos} operation.input operation.output)
      hook v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  let decoded := {st.core with pos := pos}
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hbase : (Control.base decoded).val = outer.length := by simp [decoded, Control.base, ctrls, base]
  have hpoly : Control.polymorphic decoded = p.current.ctrl.polymorphic_base := by
    simp [decoded, Control.polymorphic, ctrls]
  have hread := Numeric.read.segment operation decoded outer p.current.vals stack hbase hsize
  simp only [Numeric.read, hunary, Bool.false_eq_true, ↓reduceIte] at hread
  apply WP.spec_mono (CoreVisitor.run.spec _ hook v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ hhook)
  · intro r hr hok
    exact (hr.2 hok).choose_spec
  · apply WP.spec_mono hread
    rintro ⟨res, s⟩ ⟨hc, hp, after, hv, hlen, hout⟩
    dsimp only at hc hp hv hlen hout
    refine ⟨trivial, ?_⟩
    intro u hu
    dsimp only at hu
    subst res
    have htyped := hout.wasm2_prefix _ hC p.current.ops operation.instruction
      (by simpa [hpoly] using typed) operation.wellFormed (operation.typed _ hC)
    apply p.append_result C outer spine header base {st with core := s} operation.instruction
      p.current.ctrl.polymorphic_base after operation.wellFormed
      (by simpa [hp, decoded] using hencoded) (by simpa [hpoly] using htyped) ?_ ?_ hv hdecl
    · simpa [hc, decoded] using ctrls
    · simpa [code.BodyState.blocks_eq_of_ctrls (show s.ctrls = st.core.ctrls from hc)] using blocks

/-- Scalar extensions and the base dispatcher share the same successful-step certificate. -/
theorem Pending.extended_scalar {data env locals index st} (p : Pending data env locals index st)
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
    apply p.extended_numeric v operation (NumericExtensions.sign_properties hm).1 (NumericExtensions.sign_declared hm _) st.core.pos hsize
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
          apply p.extended_numeric v operation (NumericExtensions.saturating_unary hm) (NumericExtensions.saturating_declared hm _) next hsize
            _ (fun s _ => hv.visit_saturating v s subopcode)
          obtain ⟨bytes, hs, hn, hb, he⟩ := hd
          exact At.of_immediate p.inbounds hbyte p.pos (.saturating subopcode operation hm he)
            ⟨hs, hn, hb⟩
    · rw [code.step_extended.base visitor st.core data env ctx opcode v hm hprefix]
      exact p.scalar visitor v hv ctx hlocals opcode hscalar hsize hbyte

end Itasca.Wasm2
