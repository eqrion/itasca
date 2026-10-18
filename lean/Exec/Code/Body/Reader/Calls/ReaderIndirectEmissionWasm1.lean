import Exec.Code.Body.Relations.Calls.IndirectCallEffectsWasm1
import Exec.Code.Body.Relations.Calls.IndirectCallLowered
import Exec.Code.Local.Relations.Calls.IndirectCallMetadata
import Exec.Code.Body.Source.TypedLowering
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1

/-- The canonical reader and actual compiler callback jointly establish the
indirect-call emission, with metadata and source cursor preserved. -/
theorem reader_emit_indirect_call_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (matched : EnvTranslation.Matches env ctx C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL_INDIRECT before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
    ∃ index values emitted output,
      after.function.indirect.val = before.function.indirect.val ++ [(0#u32,index)] ∧
      ReaderPostWasm1 p out (.CALL_INDIRECT (.mk_uN 0) (.mk_uN index.val)) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.vals.val emitted output ∧
      IndirectCallEmission after.function.indirect.val C (Sequence.stackTypes st.vals.val)
        (.CALL_INDIRECT (.mk_uN 0) (.mk_uN index.val)) [emitted] output := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨index,values,callback,read,post⟩ := reader_indirect_call_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  obtain ⟨_,outer,_,_,base,_,controls,vals⟩ := p.opened
  have poly : Control.polymorphic st = false := by
    simpa [Control.polymorphic,controls] using monomorphic
  obtain ⟨ft,tt,front,typeFound,tableFound,elem,beforeTypes,concrete⟩ := reader_indirect_call_stack_wasm1 st out data env index
    outer p.current.vals vals (by simpa [Control.base,controls] using base) capacity known poly read
  have sourceType : C.TYPES[index.val]? = some ⟨.mk_list (ft.params.val.map Translate.valueType),.mk_list (ft.results.val.map Translate.valueType)⟩ := by
    simp [matched.types,List.getElem?_map,typeFound,EnvTranslation.funcType]
  have sourceTable : C.TABLES[0]? = some (.mk_tabletype (EnvTranslation.limitsType tt.limits) .FUNCREF) := by
    simp [matched.tables,List.getElem?_map,tableFound,EnvTranslation.tableType,elem,Translate.referenceType]
  change runtime.compiler.lower.FunctionCompiler.op ops before out 17#u16 index 0#u32 0#u128 = _ at callback
  rw [beforeTypes] at layout
  obtain ⟨pairs,emitted,lowered,emission⟩ := compiler_indirect_call_emission_captured ops law before after out
    (front ++ ft.results.val) env.types.val signatures C matched.types (front.map Translate.valueType)
    (ft.params.val.map Translate.valueType) (ft.results.val.map Translate.valueType) index 0#u32
    (EnvTranslation.limitsType tt.limits) sourceType sourceTable contextLocals layout reachable concrete
    (by simp) codeFits sourceFits coordinateFits callback
  refine ⟨compiler_indirect_call_ordinary_result ops law before after out index 0#u32 (.Ok ()) callback,
    compiler_indirect_call_sources ops law before after out index 0#u32 callback,
    compiler_indirect_call_cursor ops law before after out index 0#u32 callback,
    index,values,emitted,_,pairs,post,?_,beforeTypes ▸ emission⟩
  exact ⟨lowered,SourceStack.of_map (front ++ ft.results.val) concrete (by simp)⟩
end Exec.Code
