import Itasca.Runtime.Code.Body.Reader.Common.IndexedReaderCompilerBodyWasm2
import Itasca.Runtime.Code.Body.Reader.Common.ReaderRootEnd
import Itasca.Runtime.Code.Body.Reader.Common.ReaderMiscAccepted
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A successful step advances the retained canonical prefix or closes the
body. The unconsumed bytes need no independent body-encoding premise. -/
theorem IndexedTableReaderCompilerPointWasm2.advance_or_closing_of_opcode {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before middle : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st} (C : context)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial before
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max)
    (next : Usize) (advance : next.val = st.core.pos.val + 1)
    (inbounds : st.core.pos.val < data.length) (out : code.BodyState)
    (allowed : ReaderOpcode .Wasm2 data.val[st.core.pos.val])
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2
      data.val[st.core.pos.val] before = .ok (.Ok (),out,middle)) :
    (data.val[st.core.pos.val] = 11#u8 ∧ out.core.ctrls.val = []) ∨
    IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial middle
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  rcases allowed with ordinary | scope | isElse | isEnd | extra | floatBase | memoryOp | indirect | table | statefulOp | prefixed | simd | typedSelect
  · exact .inr (point.ordinary ops law contextLocals (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) metadata localsMatch next advance inbounds out sourceBound bodyBound
      _ ordinary rfl accepted)
  · exact .inr (point.scope_step ops law next advance inbounds out sourceBound signatures _ scope rfl accepted)
  · rw [isElse] at accepted
    exact .inr (point.else_ ops law next advance inbounds out initialLocals
      (by simpa only [global_simps] using isElse) (by simpa only [global_simps] using accepted))
  · rw [isEnd] at accepted
    by_cases root : st.blocks.val.length = 1
    · exact .inl ⟨isEnd,step_end_root_wasm2 (state.boundary.pending next advance inbounds)
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before middle out ctx
        (by simpa using root) accepted⟩
    · exact .inr (point.end_nested ops law next advance inbounds out initialLocals rfl root bodyBound
        (by simpa only [global_simps] using isEnd) (by simpa only [global_simps] using accepted))
  · exact .inr (point.core_extra ops law C (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals matched.globals matched.mems
      next advance inbounds out sourceBound bodyBound _ extra rfl accepted)
  · obtain ⟨op,baseOpcode,equal⟩ := float_base_opcode_of_mem floatBase
    rw [← equal] at accepted
    exact .inr (point.float_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals next advance inbounds out op baseOpcode sourceBound bodyBound equal.symm accepted)
  · have stateful := stateful_opcode_values (.inl memoryOp)
    exact .inr (point.stateful_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out _ stateful
      sourceBound bodyBound rfl accepted)
  · rw [indirect] at accepted
    exact .inr (point.indirect_call ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C)))
      matched contextLocals signatures next advance inbounds out sourceBound bodyBound indirect accepted)
  · rw [table] at accepted
    exact .inr (point.br_table ops law next advance inbounds out
      (by intro tables depths fallback stack selector start len; exact .branchTable _ _ _ _ _ _) table accepted)
  · have stateful := stateful_opcode_values (.inr statefulOp)
    exact .inr (point.stateful_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out _ stateful
      sourceBound bodyBound rfl accepted)
  · rw [prefixed] at accepted
    obtain ⟨subopcode,endPosition,decoded,choice⟩ := reader_misc_accepted
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx index before middle accepted
    rcases choice with ⟨op,extension,subopcodeEq⟩ | bulk
    · exact .inr (point.float_saturating ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals next advance inbounds out op extension
        subopcode endPosition subopcodeEq decoded sourceBound bodyBound prefixed accepted)
    · exact .inr (point.stateful_bulk ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out subopcode endPosition bulk
        sourceBound bodyBound prefixed decoded accepted)
  · rw [simd] at accepted
    exact .inr (point.simd ops law C contextLocals matched.mems (fun tables => (inferInstance : SimdEmbedding tables.simd tables.constants C (ExecutableEmission tables C))) next advance inbounds out sourceBound bodyBound simd accepted)
  · rw [typedSelect] at accepted
    exact .inr (point.typed_select ops law C (by intro tables input instruction code output h; exact .typedSelect h) contextLocals next advance inbounds out sourceBound bodyBound typedSelect accepted)
end Itasca.Runtime.Code
