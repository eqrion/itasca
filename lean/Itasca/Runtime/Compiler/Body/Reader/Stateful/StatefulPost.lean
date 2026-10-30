import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.SourceMachine.Stateful.SignatureTyping

/-!
A stateful source reader advances the exact supplied zipper in all paths; live concrete operands additionally expose its context-derived signature.

Main declarations: `StatefulReaderPost`. A direct consumer is `Compiler.Body.Reader.Acceptance.StatefulCallbackAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- A stateful source reader advances the exact supplied zipper in all paths;
live concrete operands additionally expose its context-derived signature. -/
def StatefulReaderPost {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) (out : code.OpIterState) (op : SourceMachine.Stateful.Instruction) : Prop :=
  ∃ values, Wasm2.ReaderPost p out op.source p.current.ctrl.polymorphic_base values ∧
    ∀ C, EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      ConcreteStack st.core.vals.val → p.current.ctrl.polymorphic_base = false →
      ∃ front input output, SourceMachine.Stateful.Signature C op input output ∧
        Sequence.stackTypes st.core.vals.val = front ++ input ∧
        Sequence.stackTypes out.vals.val = front ++ output ∧ ConcreteStack out.vals.val

theorem _root_.Itasca.Wasm2.MetadataReaderPost.stateful_post {data env locals index st}
    {p : Pending data env .Wasm2 locals index st} {D M : Type}
    {decode : Result (core.result.Result D error.OpError × code.OpIterState)}
    {pops : D → List wasm_types.ValueType} {output : D → Option wasm_types.ValueType}
    {metadata : D → M} {operation : D → instr} {value : M} {out : code.OpIterState}
    (post : Wasm2.MetadataReaderPost p decode pops output metadata operation value out)
    (op : SourceMachine.Stateful.Instruction)
    (source : ∀ a, metadata a = value → operation a = op.source)
    (size : st.core.vals.val.length < Usize.max) : StatefulReaderPost p out op := by
  obtain ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,sourcePost,principal⟩ := post
  refine ⟨values,by simpa only [source a metadataEq] using sourcePost,?_⟩
  intro C matched known monomorphic
  have retained : Wasm2.MetadataReaderPost p decode pops output metadata operation value out :=
    ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,sourcePost,principal⟩
  obtain ⟨b,metadataEq,front,beforeTypes,afterTypes,afterKnown,typed,_,_⟩ := retained.types known monomorphic size
  refine ⟨front,Simd.inputTypes (pops b),Simd.outputTypes (output b),?_,beforeTypes,afterTypes,afterKnown⟩
  exact SourceMachine.Stateful.Signature.of_typed (by simpa only [source b metadataEq] using typed C matched)

end Itasca.Runtime.Compiler
