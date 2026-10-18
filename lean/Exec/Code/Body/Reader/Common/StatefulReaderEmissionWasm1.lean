import Exec.Code.Body.Reader.Common.StatefulReaderPostWasm1
import Exec.Code.Local.Relations.Common.StatefulLowered
import Exec.Code.Local.Relations.Common.StatefulEffects
import Exec.Code.Body.Source.TypedLowering
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1

/-- The actual compiler callback and exact reader post determine an emitted
stateful instruction and the complete append to its function-local pair table. -/
theorem StatefulReaderPostWasm1.emission {data env ctx bt st}
    {p : Pending data env ctx bt st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPostWasm1 p out op)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (C : context) (pairs : List (U32 × U32)) (a b : U32)
    (single : statefulUsesPair op = false)
    (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (matched : EnvTranslation.Matches env ctx C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
      after.function.indirect = before.function.indirect ∧
      ∃ values emitted output, ReaderPostWasm1 p out op.source p.current.ctrl.polymorphic_base values ∧
        TypedLowered before after out.vals.val emitted output ∧
        StatefulEmission pairs C (Sequence.stackTypes st.vals.val)
          op.source [emitted] output := by
  obtain ⟨values,sourcePost,typesPost⟩ := post
  obtain ⟨front,input,output,signature,beforeTypes,afterTypes,afterKnown⟩ := typesPost C matched known monomorphic
  obtain ⟨types,concrete⟩ := (concreteStack_iff _).mp afterKnown
  have typed : types.map Translate.valueType = front ++ output := by
    simpa only [concrete,Sequence.stackTypes,List.map_map,Function.comp_def] using afterTypes
  rw [beforeTypes] at layout
  obtain ⟨pairEq,emitted,lowered,emission⟩ := compiler_stateful_single_emission ops law before after out types C front
    input output op a b signature contextLocals arguments layout reachable concrete typed codeFits sourceFits coordinateFits single callback pairs
  exact ⟨compiler_stateful_ordinary_result ops law before after out _ _ _ (.Ok ()) callback,
    compiler_stateful_sources ops law before after out _ _ _ callback,
    compiler_stateful_cursor ops law before after out _ _ _ callback,pairEq,values,emitted,front ++ output,
    sourcePost,⟨lowered,afterKnown,afterTypes⟩,beforeTypes ▸ emission⟩

end Exec.Code
