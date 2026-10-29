import Itasca.Runtime.Compiler.Body.Relations.Calls.IndirectCalls
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
The canonical reader and actual compiler callback jointly establish the indirect-call emission, with metadata and source cursor preserved.

Main declarations: `reader_emit_indirect_call_wasm2`. A direct consumer is `Compiler.Body.Reader.Calls.IndirectCallPrefix`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- The canonical reader and actual compiler callback jointly establish the
indirect-call emission, with metadata and source cursor preserved. -/
theorem reader_emit_indirect_call_wasm2 {data env locals typeIndex st}
    (p : Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ index table values emitted output,
      after.function.indirect.val = before.function.indirect.val ++ [(table,index)] ∧
      ReaderPostWasm2 p out.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted output ∧
      IndirectCallEmission after.function.indirect.val C (Sequence.stackTypes st.core.vals.val)
        (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN index.val)) [emitted] output := by
  obtain ⟨index,table,values,callback,read,post⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨_,outer,_,_,base,_,controls,_,vals⟩ := p.opened
  have poly : Control.polymorphic st.core = false := by
    simpa [Control.polymorphic,controls] using monomorphic
  obtain ⟨ft,tt,front,typeFound,tableFound,elem,beforeTypes,concrete⟩ := reader_indirect_call_stack_wasm2 st out data env index table
    outer p.current.vals vals (by simpa [Control.base,controls] using base) known poly p.opened.shape.core read
  have sourceType : C.TYPES[index.val]? = some ⟨.mk_list (ft.params.val.map Translate.valueType),.mk_list (ft.results.val.map Translate.valueType)⟩ := by
    simp [matched.types,List.getElem?_map,typeFound,EnvTranslation.funcType]
  have sourceTable : C.TABLES[table.val]? = some (.mk_tabletype (EnvTranslation.limitsType tt.limits) .FUNCREF) := by
    simp [matched.tables,List.getElem?_map,tableFound,EnvTranslation.tableType,elem,Translate.referenceType]
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 index table 0#u128 = _ at callback
  rw [beforeTypes] at layout
  obtain ⟨pairs,emitted,lowered,emission⟩ := compiler_indirect_call_emission_captured ops law before after out.core
    (front ++ ft.results.val) env.types.val signatures C matched.types (front.map Translate.valueType)
    (ft.params.val.map Translate.valueType) (ft.results.val.map Translate.valueType) index table
    (EnvTranslation.limitsType tt.limits) sourceType sourceTable contextLocals layout reachable concrete
    (by simp) codeFits sourceFits coordinateFits callback
  refine ⟨compiler_indirect_call_ordinary_result ops law before after out.core index table (.Ok ()) callback,
    compiler_indirect_call_sources ops law before after out.core index table callback,
    compiler_indirect_call_cursor ops law before after out.core index table callback,
    index,table,values,emitted,_,pairs,post,?_,beforeTypes ▸ emission⟩
  exact ⟨lowered,SourceStack.of_map (front ++ ft.results.val) concrete (by simp)⟩
end Itasca.Runtime.Code
