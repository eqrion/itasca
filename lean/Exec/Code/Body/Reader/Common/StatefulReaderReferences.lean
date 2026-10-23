import Exec.Code.Body.Reader.Common.StatefulReaderPost
import Exec.Code.Body.Reader.Common.ReaderReferenceSteps
namespace Exec.Code
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

end Exec.Code
