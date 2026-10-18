import Exec.Code.Body.Reader.Local.ReaderWasm1Local
import Exec.Code.Body.Reader.Common.ReaderMetadata
import Itasca.Wasm2.References.Step
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1

/-- Exact successful decoder and fixed-stack effect, with the original source zipper. -/
abbrev MetadataReaderPostWasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (operation : A → instr) (value : B) (out : code.OpIterState) : Prop :=
    ∃ a middle values, decode = .ok (.Ok a,middle) ∧ middle.vals = st.vals ∧
      middle.ctrls = st.ctrls ∧ metadata a = value ∧
      Wasm2.Simd.readFixed middle (pops a) (output a) = .ok (.Ok (),out) ∧
      out.ctrls = st.ctrls ∧ out.pos = middle.pos ∧
      Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals (pops a) (output a) values ∧
      ReaderPostWasm1 p out (operation a) p.current.ctrl.polymorphic_base values ∧
      (∀ C, EnvTranslation.Matches env ctx C →
        Instr_ok C (operation a) (.mk_functype (.mk_list (Wasm2.Simd.inputTypes (pops a)))
          (.mk_list (Wasm2.Simd.outputTypes (output a)))))

/-- Metadata readers preserve the supplied source zipper, retaining the exact
decoded immediate and fixed stack effect needed by compilation. -/
theorem reader_metadata_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (operation : A → instr)
    (decoded : decode ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ a, r.1 = .Ok a → At data p.start (.plain (operation a)) r.2.pos ⦄)
    (wellFormed : ∀ a, wf_instr (operation a))
    (typing : ∀ a, (∃ state, decode = .ok (.Ok a,state)) → ∀ C,
      EnvTranslation.Matches env ctx C →
      Instr_ok C (operation a) (.mk_functype (.mk_list (Wasm2.Simd.inputTypes (pops a)))
        (.mk_list (Wasm2.Simd.outputTypes (output a)))))
    (profile : ∀ a C, Wasm1.Instruction C (operation a))
    (size : st.vals.val.length < Usize.max) (value : B) (out : code.OpIterState)
    (accepted : Wasm2.metadataOperands decode pops output metadata = .ok (.Ok value,out)) :
    MetadataReaderPostWasm1 p decode pops output metadata operation value out := by
  obtain ⟨C,outer,spine,header,base,typed,ctrls,stack⟩ := p.opened
  have context := spine.matches.enter (p.current.form.label p.current.ctrl.block_type)
  obtain ⟨⟨result,middle⟩,read,valuesEq,controlsEq,encoding⟩ := WP.spec_imp_exists decoded
  dsimp only at valuesEq controlsEq encoding
  cases result with
  | Err error => simp [Wasm2.metadataOperands,read] at accepted
  | Ok a =>
    have middleBase : (Control.base middle).val = outer.length := by
      simp [Control.base,controlsEq,ctrls,base]
    have poly : Control.polymorphic middle = p.current.ctrl.polymorphic_base := by
      simp [Control.polymorphic,controlsEq,ctrls]
    obtain ⟨⟨result,final⟩,readFixed,controls,position,values,afterValues,length,effect⟩ := WP.spec_imp_exists
      (Wasm2.Simd.readFixed.segment middle (pops a) (output a) outer p.current.vals
        (by simpa [valuesEq] using stack) middleBase (by simpa [valuesEq] using size))
    dsimp only at controls position afterValues length effect
    cases result with
    | Err error => simp [Wasm2.metadataOperands,read,readFixed] at accepted
    | Ok unitValue =>
      cases unitValue
      simp only [Wasm2.metadataOperands,read,readFixed,bind_ok,uncurry_apply_pair,Result.ok.injEq,
        core.result.Result.Ok.injEq,Prod.mk.injEq] at accepted
      obtain ⟨rfl,rfl⟩ := accepted
      have finalTyped : Sequence.TypedPrefix (Frames.enter C p.current.form p.current.ctrl.block_type)
          (p.current.ops ++ [operation a]) p.current.ctrl.polymorphic_base values := by
        apply typed.append context.wf (operation a) (wellFormed a)
        intro ts realizes
        obtain ⟨front,rfl,hbefore⟩ := effect rfl ts (by simpa only [poly] using realizes)
        refine ⟨front ++ Wasm2.Simd.inputTypes (pops a),by simpa only [poly] using hbefore,?_⟩
        exact .frame _ [operation a] front _ _
          (.instr _ _ _ _ (typing a ⟨middle,read⟩ _ context) context.wf (wellFormed a))
          context.wf (by simpa [Forall] using wellFormed a)
      have sourceEncoding : At data p.start (.plain (operation a)) final.pos := by
        simpa only [position] using encoding a rfl
      have controlEq : final.ctrls.val = p.parents.map Frames.Saved.ctrl ++
          [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
        simpa [controls,controlsEq] using ctrls
      refine ⟨a,middle,values,read,valuesEq,controlsEq,rfl,readFixed,controls.trans controlsEq,position,?_,?_,typing a ⟨middle,read⟩⟩
      · simpa only [poly] using effect rfl
      · exact reader_append_context_wasm1 p C outer spine header base ctrls stack final
          (operation a) p.current.ctrl.polymorphic_base values (wellFormed a) sourceEncoding
          finalTyped controlEq afterValues length (fun C => profile a C)

end Exec.Code
