import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulPost
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEffects
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
The actual compiler callback and exact reader post determine an emitted stateful instruction and the complete append to its function-local pair table.

Main declarations: `StatefulReaderPost.emission`. A direct consumer is `Compiler.Body.Reader.Calls.IndirectPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- The actual compiler callback and exact reader post determine an emitted
stateful instruction and the complete append to its function-local pair table. -/
theorem StatefulReaderPost.emission {data env locals index st}
    {p : Pending data env .Wasm2 locals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (C : context) (a b : U32)
    (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
      (∃ extra,after.function.indirect.val = before.function.indirect.val ++ extra) ∧
      ∃ values emitted output, ReaderPostWasm2 p out op.source p.current.ctrl.polymorphic_base values ∧
        TypedLowered before after out.vals.val emitted output ∧
        StatefulEmission after.function.indirect.val C (Sequence.stackTypes st.core.vals.val)
          op.source [emitted] output := by
  obtain ⟨values,sourcePost,typesPost⟩ := post
  obtain ⟨front,input,output,signature,beforeTypes,afterTypes,afterKnown⟩ := typesPost C matched known monomorphic
  obtain ⟨types,concrete⟩ := (concrete_stack_iff _).mp afterKnown
  have typed : types.map Translate.valueType = front ++ output := by
    simpa only [concrete,Sequence.stackTypes,List.map_map,Function.comp_def] using afterTypes
  rw [beforeTypes] at layout
  obtain ⟨pairs,emitted,lowered,emission⟩ := compiler_stateful_emission ops law before after out types C front
    input output op a b signature contextLocals arguments layout reachable concrete typed codeFits sourceFits coordinateFits callback
  exact ⟨compiler_stateful_ordinary_result ops law before after out _ _ _ (.Ok ()) callback,
    compiler_stateful_sources ops law before after out _ _ _ callback,
    compiler_stateful_cursor ops law before after out _ _ _ callback,pairs,values,emitted,front ++ output,
    sourcePost,⟨lowered,afterKnown,afterTypes⟩,beforeTypes ▸ emission⟩

end Itasca.Runtime.Compiler
