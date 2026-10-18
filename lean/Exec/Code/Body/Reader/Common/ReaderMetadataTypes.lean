import Exec.Code.Body.Reader.Common.ReaderMetadata
import Exec.Code.Body.Relations.Common.KnownFixedStack
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- Live metadata readers retain the precise full operand suffix used by the
slot compiler, including values saved outside the current source scope. -/
theorem MetadataReaderPost.types {data env locals index st}
    {p : Pending data env locals index st} {A B : Type}
    {decode : Result (core.result.Result A error.OpError × code.OpIterState)}
    {pops : A → List types.ValueType} {output : A → Option types.ValueType}
    {metadata : A → B} {operation : A → instr} {value : B} {out : code.OpIterState}
    (post : MetadataReaderPost p decode pops output metadata operation value out)
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (size : st.core.vals.val.length < Usize.max) :
    ∃ a, metadata a = value ∧
      ∃ front, Sequence.stackTypes st.core.vals.val = front ++ Simd.inputTypes (pops a) ∧
        Sequence.stackTypes out.vals.val = front ++ Simd.outputTypes (output a) ∧
        ConcreteStack out.vals.val ∧
        (∀ C, EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
          Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
            (.mk_list (Simd.outputTypes (output a))))) ∧
        ∃ values, ReaderPostWasm2 p out (operation a) p.current.ctrl.polymorphic_base values := by
  obtain ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,post,principal⟩ := post
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have middleBase : (Control.base middle).val = outer.length := by
    simp [Control.base,middleControls,ctrls,base]
  have afterKnown := readFixed_known middle out outer p.current.vals (pops a) (output a)
    (by simpa only [middleValues] using stack) middleBase
    (by simpa only [middleValues] using size) (by simpa only [middleValues] using known) read
  have currentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (stack ▸ known)).2
  rw [monomorphic] at effect
  obtain ⟨front,beforeTypes,afterTypes⟩ := fixed_effect_types currentKnown effect
  obtain ⟨C',outer',spine',header',base',typed',ctrls',blocks',stack'⟩ := post.opened
  have outerEq : outer' = outer := (wasm2_spine_values spine').trans (wasm2_spine_values spine).symm
  refine ⟨a,metadataEq,Sequence.stackTypes outer ++ front,?_,?_,afterKnown,principal,values,post⟩
  · simp only [stack,Sequence.stackTypes,List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes p.current.vals = _
    rw [beforeTypes,List.append_assoc]
    rfl
  · simp only [stack',outerEq,Frames.Saved.advance,Sequence.stackTypes,List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes values = _
    rw [afterTypes,List.append_assoc]
    rfl

end Exec.Code
