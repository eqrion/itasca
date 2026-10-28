import Exec.Code.Body.Reader.Common.ReaderMetadataTypes
import Exec.Abs.Stateful.SignatureTyping
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- A stateful source reader advances the exact supplied zipper in all paths;
live concrete operands additionally expose its context-derived signature. -/
def StatefulReaderPost {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (out : code.OpIterState) (op : Abs.Stateful.Instruction) : Prop :=
  ∃ values, ReaderPostWasm2 p out op.source p.current.ctrl.polymorphic_base values ∧
    ∀ C, EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      ConcreteStack st.core.vals.val → p.current.ctrl.polymorphic_base = false →
      ∃ front input output, Abs.Stateful.Signature C op input output ∧
        Sequence.stackTypes st.core.vals.val = front ++ input ∧
        Sequence.stackTypes out.vals.val = front ++ output ∧ ConcreteStack out.vals.val

theorem MetadataReaderPost.stateful_post {data env locals index st}
    {p : Pending data env .Wasm2 locals index st} {D M : Type}
    {decode : Result (core.result.Result D error.OpError × code.OpIterState)}
    {pops : D → List types.ValueType} {output : D → Option types.ValueType}
    {metadata : D → M} {operation : D → instr} {value : M} {out : code.OpIterState}
    (post : MetadataReaderPost p decode pops output metadata operation value out)
    (op : Abs.Stateful.Instruction)
    (source : ∀ a, metadata a = value → operation a = op.source)
    (size : st.core.vals.val.length < Usize.max) : StatefulReaderPost p out op := by
  obtain ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,sourcePost,principal⟩ := post
  refine ⟨values,by simpa only [source a metadataEq] using sourcePost,?_⟩
  intro C matched known monomorphic
  have retained : MetadataReaderPost p decode pops output metadata operation value out :=
    ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,sourcePost,principal⟩
  obtain ⟨b,metadataEq,front,beforeTypes,afterTypes,afterKnown,typed,_,_⟩ := retained.types known monomorphic size
  refine ⟨front,Simd.inputTypes (pops b),Simd.outputTypes (output b),?_,beforeTypes,afterTypes,afterKnown⟩
  exact Abs.Stateful.Signature.of_typed (by simpa only [source b metadataEq] using typed C matched)

end Itasca.Runtime.Code
