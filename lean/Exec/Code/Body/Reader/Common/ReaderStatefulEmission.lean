import Exec.Code.Body.Reader.Common.ReaderMetadataTypes
import Exec.Code.Local.Relations.Common.StatefulLowered
import Exec.Code.Local.Relations.Common.StatefulEffects
import Exec.Code.Body.Source.TypedLowering
import Exec.Abs.Stateful.SignatureTyping
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- A canonical metadata reader and its actual compiler callback produce the
full typed emission, including the exact function-local pair table extension. -/
theorem MetadataReaderPost.stateful_emission {data env locals index st}
    {p : Pending data env locals index st} {D M : Type}
    {decode : Result (core.result.Result D error.OpError × code.OpIterState)}
    {pops : D → List types.ValueType} {output : D → Option types.ValueType}
    {metadata : D → M} {operation : D → instr} {value : M} {out : code.OpIterState}
    (post : MetadataReaderPost p decode pops output metadata operation value out)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (C : context)
    (instruction : D → Abs.Stateful.Instruction) (first second : D → U32)
    (source : ∀ a, operation a = (instruction a).source)
    (arguments : ∀ a, metadata a = value → StatefulArguments (instruction a) (first a) (second a))
    (callback : ∀ a, metadata a = value →
      runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode (instruction a))
        (first a) (second a) 0#u128 = .ok (.Ok (),after))
    (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true) (size : st.core.vals.val.length < Usize.max)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
      (∃ extra,after.function.indirect.val = before.function.indirect.val ++ extra) ∧
      ∃ a front values emitted, metadata a = value ∧
        Sequence.stackTypes st.core.vals.val = front ++ Simd.inputTypes (pops a) ∧
        ReaderPostWasm2 p out (instruction a).source p.current.ctrl.polymorphic_base values ∧
        TypedLowered before after out.vals.val emitted (front ++ Simd.outputTypes (output a)) ∧
        StatefulEmission after.function.indirect.val C (front ++ Simd.inputTypes (pops a))
          (instruction a).source [emitted] (front ++ Simd.outputTypes (output a)) := by
  obtain ⟨a,metadataEq,front,beforeTypes,afterTypes,afterKnown,principal,values,sourcePost⟩ :=
    post.types known monomorphic size
  have accepted := callback a metadataEq
  have signature := Abs.Stateful.Signature.of_typed
    (show Instr_ok C (instruction a).source
      (.mk_functype (.mk_list (Simd.inputTypes (pops a))) (.mk_list (Simd.outputTypes (output a)))) by
      simpa only [source a] using principal C matched)
  obtain ⟨types,concrete⟩ := (concreteStack_iff _).mp afterKnown
  have typed : types.map Translate.valueType = front ++ Simd.outputTypes (output a) := by
    simpa only [concrete,Sequence.stackTypes,List.map_map,Function.comp_def] using afterTypes
  rw [beforeTypes] at layout
  obtain ⟨pairs,emitted,lowered,emission⟩ := compiler_stateful_emission ops law before after out types C front
    (Simd.inputTypes (pops a)) (Simd.outputTypes (output a)) (instruction a) (first a) (second a)
    signature contextLocals (arguments a metadataEq) layout reachable concrete typed codeFits sourceFits coordinateFits accepted
  exact ⟨compiler_stateful_ordinary_result ops law before after out _ _ _ (.Ok ()) accepted,
    compiler_stateful_sources ops law before after out _ _ _ accepted,
    compiler_stateful_cursor ops law before after out _ _ _ accepted,pairs,a,front,values,emitted,metadataEq,
    beforeTypes,by simpa only [source a] using sourcePost,⟨lowered,afterKnown,afterTypes⟩,emission⟩

end Exec.Code
