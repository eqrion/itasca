import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Binary.Body.EncodingUnique
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Body.References.Reader
import Itasca.Runtime.Compiler.Body.Relations.KnownFixedStack

/-! ## PostDeclared -/

section

/-!
Exact byte provenance identifies the retained instruction with the canonical accepted trace, so declared-reference evidence is recovered from the reader.

Main declarations: `Body.ReaderPost.declared`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Exact byte provenance identifies the retained instruction with the canonical
accepted trace, so declared-reference evidence is recovered from the reader. -/
theorem _root_.Itasca.Body.ReaderPost.declared {data env locals index st out instruction poly values}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderPost p out instruction poly values) :
    Spec.DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction := by
  have consumed := Body.Consumed.snoc p.consumed post.encoded
  have all : Body.TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
      (Body.Frames.trace p.parents p.current ++ [.plain instruction]) := by
    cases post.after.1 with
    | running ft parents current signature bounds opened bodyType canonical declared =>
      rw [consumed.unique canonical]
      exact declared
    | closed ft ops tokens signature bounds controls blocks body typed canonical declared =>
      rw [consumed.unique canonical]
      exact declared
  simpa only [Body.tokens_declared_singleton,Body.Token.Declared] using
    ((Body.tokens_declared_append _ _ _).mp all).2

end Itasca.Compiler

end

/-! ## Span -/

section

/-!
Byte-coordinate spans consumed by accepted reader steps.

Main declarations: `reader_span` and `Body.ReaderPost.span`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_span {data env locals index st token next}
    (p : Body.Pending data env locals index st) (encoded : Body.At data p.start token next) :
    st.core.pos.val ≤ next.val ∧ next.val ≤ data.length := by
  have span := encoded.span
  have pos := p.pos
  exact ⟨by omega, span.2⟩

theorem _root_.Itasca.Body.ReaderPost.span {data env locals index st out instruction poly values}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderPost p out instruction poly values) :
    st.core.pos.val ≤ out.pos.val ∧ out.pos.val ≤ data.length := reader_span p post.encoded

end Itasca.Compiler

end

/-! ## MetadataTypes -/

section

/-!
Live metadata readers retain the precise full operand suffix used by the slot compiler, including values saved outside the current source scope.

Main declarations: `Body.MetadataReaderPost.types`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

/-- Live metadata readers retain the precise full operand suffix used by the
slot compiler, including values saved outside the current source scope. -/
theorem _root_.Itasca.Body.MetadataReaderPost.types {data env locals index st}
    {p : Pending data env locals index st} {A B : Type}
    {decode : Result (core.result.Result A error.OpError × code.OpIterState)}
    {pops : A → List wasm_types.ValueType} {output : A → Option wasm_types.ValueType}
    {metadata : A → B} {operation : A → instr} {value : B} {out : code.OpIterState}
    (post : Body.MetadataReaderPost p decode pops output metadata operation value out)
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (size : st.core.vals.val.length < Usize.max) :
    ∃ a, metadata a = value ∧
      ∃ front, Body.Stack.stackTypes st.core.vals.val = front ++ Simd.inputTypes (pops a) ∧
        Body.Stack.stackTypes out.vals.val = front ++ Simd.outputTypes (output a) ∧
        ConcreteStack out.vals.val ∧
        (∀ C, Translation.Environment.Matches env ⟨locals,p.ft.results⟩ C →
          Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
            (.mk_list (Simd.outputTypes (output a))))) ∧
        ∃ values, Body.ReaderPost p out (operation a) p.current.ctrl.polymorphic_base values := by
  obtain ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,post,principal⟩ := post
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,stack⟩ := p.opened
  have middleBase : (Body.Control.base middle).val = outer.length := by
    simp [Body.Control.base,middleControls,ctrls,base]
  have afterKnown := read_fixed_known middle out outer p.current.vals (pops a) (output a)
    (by simpa only [middleValues] using stack) middleBase
    (by simpa only [middleValues] using size) (by simpa only [middleValues] using known) read
  have currentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (stack ▸ known)).2
  rw [monomorphic] at effect
  obtain ⟨front,beforeTypes,afterTypes⟩ := fixed_effect_types currentKnown effect
  obtain ⟨C',outer',spine',header',base',typed',ctrls',blocks',stack'⟩ := post.opened
  have outerEq : outer' = outer := (spine_values spine').trans (spine_values spine).symm
  refine ⟨a,metadataEq,Body.Stack.stackTypes outer ++ front,?_,?_,afterKnown,principal,values,post⟩
  · simp only [stack,Body.Stack.stackTypes,List.map_append]
    change Body.Stack.stackTypes outer ++ Body.Stack.stackTypes p.current.vals = _
    rw [beforeTypes,List.append_assoc]
    rfl
  · simp only [stack',outerEq,Frames.Saved.advance,Body.Stack.stackTypes,List.map_append]
    change Body.Stack.stackTypes outer ++ Body.Stack.stackTypes values = _
    rw [afterTypes,List.append_assoc]
    rfl

end Itasca.Compiler

end
