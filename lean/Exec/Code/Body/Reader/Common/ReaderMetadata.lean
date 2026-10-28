import Exec.Code.Body.Reader.Common.ReaderWasm2
import Itasca.Wasm2.References.Step
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- Exact successful decoder and fixed-stack effect, with the original source zipper. -/
abbrev MetadataReaderPost {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (operation : A → instr) (value : B) (out : code.OpIterState) : Prop :=
    ∃ a middle values, decode = .ok (.Ok a,middle) ∧ middle.vals = st.core.vals ∧
      middle.ctrls = st.core.ctrls ∧ metadata a = value ∧
      Simd.readFixed middle (pops a) (output a) = .ok (.Ok (),out) ∧
      out.ctrls = st.core.ctrls ∧ out.pos = middle.pos ∧
      Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals (pops a) (output a) values ∧
      ReaderPostWasm2 p out (operation a) p.current.ctrl.polymorphic_base values ∧
      (∀ C, EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
        Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
          (.mk_list (Simd.outputTypes (output a)))))

/-- Metadata readers preserve the supplied source zipper, retaining the exact
decoded immediate and fixed stack effect needed by compilation. -/
theorem reader_metadata_wasm2 {data env locals index st}
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
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have context := (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  obtain ⟨⟨result,middle⟩,read,valuesEq,controlsEq,encoding⟩ := WP.spec_imp_exists decoded
  dsimp only at valuesEq controlsEq encoding
  cases result with
  | Err error => simp [metadataOperands,read] at accepted
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
    | Err error => simp [metadataOperands,read,readFixed] at accepted
    | Ok unitValue =>
      cases unitValue
      simp only [metadataOperands,read,readFixed,bind_ok,uncurry_apply_pair,Result.ok.injEq,
        core.result.Result.Ok.injEq,Prod.mk.injEq] at accepted
      obtain ⟨rfl,rfl⟩ := accepted
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
      · refine ⟨sourceEncoding,?_,?_⟩
        · exact ⟨C,outer,spine,⟨header.kind,header.inputs,header.outputs,
          header.prior,.simple header.emits (.plain (operation a) (wellFormed a))⟩,
          base,finalTyped,controlEq,newBlocks,afterValues⟩
        · exact p.append_result C outer spine header base {st with core := final} (operation a)
            p.current.ctrl.polymorphic_base values (wellFormed a) sourceEncoding finalTyped
            controlEq newBlocks afterValues (fun h => nomatch h) (declared a ⟨middle,read⟩)

end Itasca.Runtime.Code
