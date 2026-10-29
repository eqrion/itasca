import Itasca.Runtime.Compiler.Body.Reader.Replay.Metadata
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulPost

/-!
Reference-reader inversion and stateful postconditions for ref.func and ref.is_null, retaining the declared-reference obligation.
-/

/-! ## Reader Reference Steps -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_ref_func_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (idx : U32) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 210#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_func st.core data env = .ok (.Ok idx,out)) :
    idx.val < env.func_types.val.length ∧ out.ctrls = st.core.ctrls ∧
      out.vals.val = st.core.vals.val ++ [.Val .FuncRef] ∧
      ReaderPostWasm2 p out (.REF_FUNC (.mk_uN idx.val)) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .FuncRef]) := by
  have checked := code.read_ref_func.spec st.core data env size
  rw [accepted,WP.spec_ok] at checked
  obtain ⟨decoded,bound,declared,values⟩ := checked.2 idx rfl
  have controls := checked.1
  dsimp only at controls values
  refine ⟨bound,controls,values,?_⟩
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have matched := (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  obtain ⟨bytes,encodedBytes,length,byteBound,encoding⟩ := decoded
  have encoded : At data p.start (.plain (.REF_FUNC (.mk_uN idx.val))) out.pos :=
    .of_immediate p.inbounds byte p.pos (.reference (.refFunc idx encoding)) ⟨encodedBytes,length,byteBound⟩
  have wf : wf_instr (.REF_FUNC (.mk_uN idx.val)) := .instr_case_41 _ (EnvTranslation.index_wf idx)
  have newTyped := typed.append matched.wf _ wf (by
    intro ts realized
    obtain ⟨front,prior,rfl⟩ := (Sequence.realizes_append_concrete _ _ [.FuncRef] ts).mp realized
    exact ⟨front,prior,by simpa [Frames.enter,Translate.valueType] using
      (Instrs_ok.frame _ _ front [] [.FUNCREF]
        (.instr _ _ [] [.FUNCREF] (matched.ref_func idx bound) matched.wf wf)
        matched.wf (by simpa [Forall] using wf))⟩)
  have newControls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
    simpa [controls] using ctrls
  have newBlocks : ({st with core := out} : code.BodyState).blocks.val =
      p.parents.map Frames.Saved.bt ++ [p.current.bt] := by
    simpa [code.BodyState.blocks_eq_of_ctrls controls] using blocks
  have newValues : out.vals.val = outer ++ (p.current.vals ++ [.Val .FuncRef]) := by
    simpa [stack,List.append_assoc] using values
  refine ⟨encoded,?_,?_⟩
  · exact ⟨C,outer,spine,⟨header.kind,header.inputs,header.outputs,
      header.prior,.simple header.emits (.plain _ wf)⟩,base,newTyped,newControls,newBlocks,newValues⟩
  · exact p.append_result C outer spine header base {st with core := out} _
      p.current.ctrl.polymorphic_base _ wf encoded newTyped newControls newBlocks newValues (fun h => nomatch h) declared

theorem reader_ref_is_null_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 209#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_is_null st.core = .ok (.Ok (),out)) :
    out.ctrls = st.core.ctrls ∧ out.pos = st.core.pos ∧
      ∃ rt values, Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        [ModuleConstants.referenceValueType rt] (some .I32) values ∧
        ReaderPostWasm2 p out .REF_IS_NULL p.current.ctrl.polymorphic_base values := by
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have matched := (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  have baseEq : (Control.base st.core).val = outer.length := by simp [Control.base,ctrls,base]
  have poly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic,ctrls]
  have checked := code.read_ref_is_null.segment st.core outer p.current.vals stack baseEq size
  rw [accepted,WP.spec_ok] at checked
  obtain ⟨controls,position,values,newValues,effect⟩ := checked
  dsimp only at controls position newValues effect
  obtain ⟨rt,effect⟩ := effect rfl
  rw [poly] at effect
  have newTyped := effect.wasm2_prefix _ matched.wf _ p.current.ops .REF_IS_NULL typed .instr_case_42
    (by simpa [Simd.inputTypes,Simd.outputTypes,reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using
      Instr_ok.ref_is_null _ (Translate.referenceType rt) matched.wf .instr_case_42)
  have encoded : At data p.start (.plain .REF_IS_NULL) out.pos := by
    apply At.of_immediate p.inbounds byte p.pos (.reference .refIsNull)
    exact ⟨by simp [position],by simp [position],by have := p.pos; have := p.inbounds; simp only [position]; omega⟩
  have newControls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
    simpa [controls] using ctrls
  have newBlocks : ({st with core := out} : code.BodyState).blocks.val =
      p.parents.map Frames.Saved.bt ++ [p.current.bt] := by
    simpa [code.BodyState.blocks_eq_of_ctrls controls] using blocks
  refine ⟨controls,position,rt,values,effect,encoded,?_,?_⟩
  · exact ⟨C,outer,spine,⟨header.kind,header.inputs,header.outputs,
      header.prior,.simple header.emits (.plain .REF_IS_NULL .instr_case_42)⟩,
      base,newTyped,newControls,newBlocks,newValues⟩
  · exact p.append_result C outer spine header base {st with core := out} .REF_IS_NULL
      p.current.ctrl.polymorphic_base values .instr_case_42 encoded newTyped newControls newBlocks newValues
      (fun h => nomatch h) (by simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices])

end Itasca.Runtime.Code

end

/-! ## Stateful Reader References -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

private theorem fixed_effect_concrete {before after inputs output}
    (known : ConcreteStack before) (effect : Simd.FixedEffect false before inputs output after) :
    ConcreteStack after := by
  obtain ⟨front,afterTypes,beforeRealized⟩ := effect _ (Sequence.realizes_default false after)
  have beforeConcrete := concrete_realization known beforeRealized
  apply stackTypes_concrete
  rw [afterTypes]
  intro member
  rcases List.mem_append.mp member with member | member
  · exact beforeConcrete (List.mem_append_left _ member)
  · cases output with
    | none => simp [Simd.outputTypes] at member
    | some ty => cases ty <;> simp [Simd.outputTypes,Translate.valueType] at member

/-- Reference tests derive their concrete live suffix from the canonical fixed
effect; dead polymorphic paths only retain the exact source zipper. -/
theorem reader_ref_is_null_post_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 209#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_is_null st.core = .ok (.Ok (),out)) :
    StatefulReaderPost p out .refIsNull := by
  obtain ⟨controls,position,rt,values,effect,post⟩ := reader_ref_is_null_wasm2 p out byte size accepted
  refine ⟨values,post,?_⟩
  intro C matched known monomorphic
  obtain ⟨sourceC,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  obtain ⟨outerKnown,currentKnown⟩ := concreteStack_append.mp (stack ▸ known)
  rw [monomorphic] at effect
  obtain ⟨front,beforeTypes,afterTypes⟩ := fixed_effect_types currentKnown effect
  have afterKnown := fixed_effect_concrete currentKnown effect
  obtain ⟨C',outer',spine',header',base',typed',ctrls',blocks',stack'⟩ := post.opened
  have outerEq : outer' = outer := (wasm2_spine_values spine').trans (wasm2_spine_values spine).symm
  refine ⟨Sequence.stackTypes outer ++ front,Simd.inputTypes [ModuleConstants.referenceValueType rt],
    Simd.outputTypes (some .I32),?_,?_,?_,?_⟩
  · simpa [Simd.inputTypes,Simd.outputTypes,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.map_cons,List.map_nil,reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using
      Abs.Stateful.Signature.refIsNull (C := C) (Translate.referenceType rt)
  · simp only [stack,Sequence.stackTypes,List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes p.current.vals = _
    rw [beforeTypes,List.append_assoc]
    rfl
  · simp only [stack',outerEq,Frames.Saved.advance,Sequence.stackTypes,List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes values = _
    rw [afterTypes,List.append_assoc]
    rfl
  · simp only [stack',outerEq,Frames.Saved.advance]
    exact concreteStack_append.mpr ⟨outerKnown,afterKnown⟩

theorem reader_ref_func_post_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (idx : U32) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 210#u8)
    (size : st.core.vals.val.length < Usize.max)
    (accepted : code.read_ref_func st.core data env = .ok (.Ok idx,out)) :
    StatefulReaderPost p out (.refFunc idx.val) := by
  obtain ⟨bound,controls,values,post⟩ := reader_ref_func_wasm2 p idx out byte size accepted
  refine ⟨_,post,?_⟩
  intro C matched known _
  refine ⟨Sequence.stackTypes st.core.vals.val,[],[valtype.FUNCREF],?_,by simp,?_,?_⟩
  · apply Abs.Stateful.Signature.refFunc idx.val (EnvTranslation.funcType env.func_types.val[idx.val])
    simp [matched.funcs,List.getElem?_eq_getElem bound]
  · simp [values,Sequence.stackTypes,Translate.valueType]
  · rw [values]
    exact concreteStack_append.mpr ⟨known,by simp [ConcreteStack]⟩

end Itasca.Runtime.Code

end
