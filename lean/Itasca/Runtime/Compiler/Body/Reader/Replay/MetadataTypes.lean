import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Binary.Wasm2.EncodingUnique
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeWasm2
import Itasca.Wasm2.References.Reader
import Itasca.Wasm2.References.Step
import Itasca.Runtime.Compiler.Body.Relations.Stacks.KnownFixedStack

/-!
Sections, each formerly its own module: PostDeclared, Span, MetadataTypes.
-/

/-! ## PostDeclared -/

section

/-!
Exact byte provenance identifies the retained instruction with the canonical accepted trace, so declared-reference evidence is recovered from the reader.

Main declarations: `Wasm2.ReaderPost.declared`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedStateful`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Exact byte provenance identifies the retained instruction with the canonical
accepted trace, so declared-reference evidence is recovered from the reader. -/
theorem _root_.Itasca.Wasm2.ReaderPost.declared {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderPost p out instruction poly values) :
    DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction := by
  have consumed := Wasm2.Consumed.snoc p.consumed post.encoded
  have all : Wasm2.TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
      (Wasm2.Frames.trace p.parents p.current ++ [.plain instruction]) := by
    cases post.after.1 with
    | running ft parents current signature bounds opened bodyType canonical declared =>
      rw [consumed.unique canonical]
      exact declared
    | closed ft ops tokens signature bounds controls blocks body typed canonical declared =>
      rw [consumed.unique canonical]
      exact declared
  simpa only [Wasm2.tokensDeclared_singleton,Wasm2.Token.Declared] using
    ((Wasm2.tokensDeclared_append _ _ _).mp all).2

end Itasca.Runtime.Compiler

end

/-! ## Span -/

section

/-!
Byte-coordinate spans consumed by accepted reader steps.

Main declarations: `reader_span_wasm2` and `Wasm2.ReaderPost.span`. A direct consumer is `Compiler.Body.Reader.Calls.Compilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_span_wasm2 {data env locals index st token next}
    (p : Wasm2.Pending data env locals index st) (encoded : Wasm2.At data p.start token next) :
    st.core.pos.val ≤ next.val ∧ next.val ≤ data.length := by
  have span := encoded.span
  have pos := p.pos
  exact ⟨by omega, span.2⟩

theorem _root_.Itasca.Wasm2.ReaderPost.span {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderPost p out instruction poly values) :
    st.core.pos.val ≤ out.pos.val ∧ out.pos.val ≤ data.length := reader_span_wasm2 p post.encoded

end Itasca.Runtime.Compiler

end

/-! ## MetadataTypes -/

section

/-!
Live metadata readers retain the precise full operand suffix used by the slot compiler, including values saved outside the current source scope.

Main declarations: `Wasm2.MetadataReaderPost.types`. A direct consumer is `Compiler.Body.Reader.Stateful.StatefulPost`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- Live metadata readers retain the precise full operand suffix used by the
slot compiler, including values saved outside the current source scope. -/
theorem _root_.Itasca.Wasm2.MetadataReaderPost.types {data env locals index st}
    {p : Pending data env locals index st} {A B : Type}
    {decode : Result (core.result.Result A error.OpError × code.OpIterState)}
    {pops : A → List wasm_types.ValueType} {output : A → Option wasm_types.ValueType}
    {metadata : A → B} {operation : A → instr} {value : B} {out : code.OpIterState}
    (post : Wasm2.MetadataReaderPost p decode pops output metadata operation value out)
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
        ∃ values, Wasm2.ReaderPost p out (operation a) p.current.ctrl.polymorphic_base values := by
  obtain ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,post,principal⟩ := post
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have middleBase : (Control.base middle).val = outer.length := by
    simp [Control.base,middleControls,ctrls,base]
  have afterKnown := read_fixed_known middle out outer p.current.vals (pops a) (output a)
    (by simpa only [middleValues] using stack) middleBase
    (by simpa only [middleValues] using size) (by simpa only [middleValues] using known) read
  have currentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (stack ▸ known)).2
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

end Itasca.Runtime.Compiler

end
