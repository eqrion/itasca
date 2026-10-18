import Exec.Code.Body.Reader.Common.ReaderMetadataTypesWasm1
import Exec.Abs.Stateful.SignatureTyping
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1

/-- A stateful source reader advances the exact supplied zipper in all paths;
live concrete operands additionally expose its context-derived signature. -/
def StatefulReaderPostWasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) (out : code.OpIterState) (op : Abs.Stateful.Instruction) : Prop :=
  ∃ values, ReaderPostWasm1 p out op.source p.current.ctrl.polymorphic_base values ∧
    ∀ C, EnvTranslation.Matches env ctx C →
      ConcreteStack st.vals.val → p.current.ctrl.polymorphic_base = false →
      ∃ front input output, Abs.Stateful.Signature C op input output ∧
        Sequence.stackTypes st.vals.val = front ++ input ∧
        Sequence.stackTypes out.vals.val = front ++ output ∧ ConcreteStack out.vals.val

theorem MetadataReaderPostWasm1.stateful_post {data env ctx bt st}
    {p : Pending data env ctx bt st} {D M : Type}
    {decode : Result (core.result.Result D error.OpError × code.OpIterState)}
    {pops : D → List types.ValueType} {output : D → Option types.ValueType}
    {metadata : D → M} {operation : D → instr} {value : M} {out : code.OpIterState}
    (post : MetadataReaderPostWasm1 p decode pops output metadata operation value out)
    (op : Abs.Stateful.Instruction)
    (source : ∀ a, metadata a = value → operation a = op.source)
    (size : st.vals.val.length < Usize.max) : StatefulReaderPostWasm1 p out op := by
  obtain ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,sourcePost,principal⟩ := post
  refine ⟨values,by simpa only [source a metadataEq] using sourcePost,?_⟩
  intro C matched known monomorphic
  have retained : MetadataReaderPostWasm1 p decode pops output metadata operation value out :=
    ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,sourcePost,principal⟩
  obtain ⟨b,metadataEq,front,beforeTypes,afterTypes,afterKnown,typed,_,_⟩ := retained.types known monomorphic size
  refine ⟨front,Wasm2.Simd.inputTypes (pops b),Wasm2.Simd.outputTypes (output b),?_,beforeTypes,afterTypes,afterKnown⟩
  exact Abs.Stateful.Signature.of_typed (by simpa only [source b metadataEq] using typed C matched)

end Exec.Code
