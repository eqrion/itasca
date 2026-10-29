import Itasca.Wasm2.References.Operands
import Itasca.Wasm2.References.EnvMatches
import Itasca.Wasm2.Scalar.ReaderPost

/-!
Shared metadata decoding, fixed-stack effects, and exact source-prefix advancement.
Reference, table, and bulk-memory preservation and compiler inversion use the same
reader specification, with explicit declared-reference evidence.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

/-- Exact successful decoder and fixed-stack effect, with the original source zipper. -/
abbrev MetadataReaderPost {data env profile locals index st}
    (p : Pending data env profile locals index st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (operation : A → instr) (value : B) (out : code.OpIterState) : Prop :=
    ∃ a middle values, decode = .ok (.Ok a,middle) ∧ middle.vals = st.core.vals ∧
      middle.ctrls = st.core.ctrls ∧ metadata a = value ∧
      Simd.readFixed middle (pops a) (output a) = .ok (.Ok (),out) ∧
      out.ctrls = st.core.ctrls ∧ out.pos = middle.pos ∧
      Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals (pops a) (output a) values ∧
      Wasm2.ReaderPost p out (operation a) p.current.ctrl.polymorphic_base values ∧
      (∀ C, EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
        Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
          (.mk_list (Simd.outputTypes (output a)))))

theorem Pending.metadata_reader {data env profile locals index st}
    (p : Pending data env profile locals index st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (operation : A → instr)
    (decoded : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → At data p.start (.plain (operation a)) r.2.pos ⦄)
    (wellFormed : ∀ a, wf_instr (operation a))
    (typing : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → ∀ C,
      EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
        (.mk_list (Simd.outputTypes (output a)))))
    (declared : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (operation a))
    (size : st.core.vals.val.length < Usize.max) (hwasm2 : profile ≠ .Wasm1) :
    metadataOperands decode pops output metadata ⦃ r => ∀ value, r.1 = .Ok value →
      MetadataReaderPost p decode pops output metadata operation value r.2 ⦄ := by
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have context := (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  obtain ⟨⟨result,middle⟩,read,valuesEq,controlsEq,encoding⟩ := WP.spec_imp_exists decoded
  dsimp only at valuesEq controlsEq encoding
  cases result with
  | Err error => simp [metadataOperands,read]
  | Ok a =>
    have middleBase : (Control.base middle).val = outer.length := by
      simp [Control.base,controlsEq,ctrls,base]
    have poly : Control.polymorphic middle = p.current.ctrl.polymorphic_base := by
      simp [Control.polymorphic,controlsEq,ctrls]
    obtain ⟨⟨result,final⟩,readFixed,controls,position,values,afterValues,length,effect⟩ := WP.spec_imp_exists
      (Simd.readFixed.segment middle (pops a) (output a) outer p.current.vals
        (by simpa [valuesEq] using stack) middleBase (by simpa [valuesEq] using size))
    dsimp only at controls position afterValues length effect
    cases result with
    | Err error => simp [metadataOperands,read,readFixed]
    | Ok unitValue =>
      cases unitValue
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (metadata a),final), by simp [metadataOperands,read,readFixed], ?_⟩
      intro value accepted
      have same : metadata a = value := by simpa using accepted
      subst value
      have newTyped := (effect rfl).wasm2_prefix _ context.wf _ p.current.ops (operation a)
        (by simpa [poly,Frames.enter] using typed) (wellFormed a) (typing a ⟨middle,read⟩ _ context)
      have finalTyped := newTyped
      rw [poly] at finalTyped
      have sourceEncoding : At data p.start (.plain (operation a)) final.pos := by
        simpa only [position] using encoding a rfl
      have controlEq : final.ctrls.val = p.parents.map Frames.Saved.ctrl ++
          [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
        simpa [controls,controlsEq] using ctrls
      have newBlocks : ({st with core := final} : code.BodyState).blocks.val =
          p.parents.map Frames.Saved.bt ++ [p.current.bt] := by
        simpa [controls,controlsEq,ctrls] using blocks
      refine ⟨a,middle,values,read,valuesEq,controlsEq,rfl,readFixed,controls.trans controlsEq,position,?_,?_,typing a ⟨middle,read⟩⟩
      · simpa only [poly] using effect rfl
      · exact p.append_reader_context C outer spine header base final (operation a)
          p.current.ctrl.polymorphic_base values (wellFormed a) sourceEncoding finalTyped
          controlEq newBlocks afterValues (declared a ⟨middle,read⟩) (fun hp => absurd hp hwasm2)

theorem Pending.metadata_reader_accepted {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (operation : A → instr)
    (decoded : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → At data p.start (.plain (operation a)) r.2.pos ⦄)
    (wellFormed : ∀ a, wf_instr (operation a))
    (typing : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → ∀ C,
      EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
        (.mk_list (Simd.outputTypes (output a)))))
    (declared : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (operation a))
    (size : st.core.vals.val.length < Usize.max) (value : B) (out : code.OpIterState)
    (accepted : metadataOperands decode pops output metadata = .ok (.Ok value,out)) :
    MetadataReaderPost p decode pops output metadata operation value out := by
  have effect := p.metadata_reader decode pops output metadata operation decoded wellFormed typing declared size (by intro h; cases h)
  rw [accepted, WP.spec_ok] at effect
  exact effect value rfl

end Itasca.Wasm2
