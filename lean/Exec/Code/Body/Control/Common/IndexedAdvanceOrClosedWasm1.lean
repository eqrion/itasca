import Exec.Code.Body.Reader.Common.IndexedReaderCompilerBodyWasm1
import Exec.Code.Body.Control.Common.IndexedEndOrClosed
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm1.advance_or_closed_of_opcode {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before middle : runtime.compiler.FunctionCompiler A}
    {locals data env ctx bodyBt st} (C : context)
    (point : IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial before
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ctx C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max)
    (next : Usize) (advance : next.val = st.pos.val + 1)
    (inbounds : st.pos.val < data.length) (out : code.OpIterState)
    (allowed : FloatCoreOpcode data.val[st.pos.val] ∨ data.val[st.pos.val].val ∈ [63,64] ∨
      data.val[st.pos.val] = 17#u8 ∨ data.val[st.pos.val] = 14#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx data.val[st.pos.val] before = .ok (.Ok (),out,middle)) :
    out.ctrls.val = [] ∨
    IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial middle
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  rcases allowed with legacy | memory | indirect | table
  · rcases legacy with core | floatBase | prefixed
    · rcases core with allowed | extra
      · rcases allowed.partition with ordinary | scope | isElse | isEnd
        · exact .inr (point.ordinary ops law contextLocals
            (fun tables => (inferInstance : CumulativeEmbedding tables.indirect C (ExecutableEmission tables C)))
            metadata localsMatch next advance inbounds out sourceBound bodyBound bodyResults _ ordinary rfl accepted)
        · exact .inr (point.scope_step ops law next advance inbounds out sourceBound _ scope rfl accepted)
        · rw [isElse] at accepted
          exact .inr (point.else_ ops law next advance inbounds out initialLocals
            (by simpa only [global_simps] using isElse) (by simpa only [global_simps] using accepted))
        · rw [isEnd] at accepted
          exact point.end_or_closed ops law initialLocals next advance inbounds out
            bodyBound isEnd accepted
      · exact .inr (point.core_extra ops law C
          (fun tables => (inferInstance : CumulativeEmbedding tables.indirect C (ExecutableEmission tables C)))
          contextLocals matched.globals matched.mems next advance inbounds out sourceBound bodyBound _ extra rfl accepted)
    · obtain ⟨op,baseOpcode,equal⟩ := float_base_opcode_of_mem floatBase
      rw [← equal] at accepted
      exact .inr (point.float_base ops law
        (fun tables => (inferInstance : CumulativeEmbedding tables.indirect C (ExecutableEmission tables C)))
        contextLocals next advance inbounds out op baseOpcode sourceBound bodyBound equal.symm accepted)
    · rw [prefixed] at accepted
      exact False.elim (float_saturating_wasm1_impossible
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before middle
        {st with pos := next} out data env ctx accepted)
  · exact .inr (point.memory_metadata ops law
      (fun tables => (inferInstance : CumulativeEmbedding tables.indirect C (ExecutableEmission tables C)))
      matched contextLocals next advance inbounds out _ memory sourceBound bodyBound rfl accepted)
  · rw [indirect] at accepted
    exact .inr (point.indirect_call ops law
      (fun tables => (inferInstance : CumulativeEmbedding tables.indirect C (ExecutableEmission tables C)))
      matched contextLocals signatures next advance inbounds out sourceBound bodyBound indirect accepted)
  · rw [table] at accepted
    exact .inr (point.br_table ops law next advance inbounds out
      (by intro tables depths fallback stack selector start len; exact .branchTable _ _ _ _ _ _)
      (by simpa only [code.OP_BR_TABLE] using table) (by simpa only [code.OP_BR_TABLE] using accepted))
end Exec.Code
