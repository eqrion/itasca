import Exec.Code.Body.Control.Memory.IndexedTablePointMemoryWasm1
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerFold
import Exec.Code.Body.Control.Table.IndexedTablePointIndirectCall
import Exec.Code.Body.Control.Table.IndexedTablePointNumericWasm1
import Exec.Code.Body.Control.Table.IndexedTablePointOrdinaryWasm1
import Exec.Code.Body.Control.Table.IndexedTablePointControlWasm1
import Exec.Code.Body.Control.Table.IndexedTablePointRootWasm1
import Exec.Code.Body.Control.Table.IndexedTablePointExtraWasm1
import Exec.Code.Body.Reader.Table.IndexedTableReaderTable
import Exec.Code.Local.Relations.Common.ExecutableWasm1Opcodes
import Exec.Code.Body.Relations.Common.ExecutableEmission
import Exec.Code.Body.Reader.Common.ReaderOpcodePartition
import Exec.Code.Body.Reader.Common.ReaderCompilerBounds
import Exec.Code.Body.Lowering.Float.FloatWasm1Exclusion
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Complete-profile Wasm1 validation produces code evidence indexed by the
actual final function tables, without a source-language subset premise. -/
theorem TypedRunWasm1.compile_executable {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx bodyBt st source}
    (C : context)
    (run : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt st before final)
    (point : IndexedTableReaderCompilerPointWasm1 (fun tables => ExecutableEmission tables C) initial before
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
    (encoded : Wasm1.BodyEncoding data source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ctx C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    StructuredCompiledBodyWithTables final.function.jump_tables.val
      (ExecutableEmission (CompilerTables.ofFunction final.function) C) initial final
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ctx.results.val.map Translate.valueType) locals source := by
  apply TypedRunWasm1.fold_indexed_tables ops (fun tables => ExecutableEmission tables C) initial _ _ _ _ data env ctx bodyBt source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := encoded.next_executable_wasm1_opcode state.boundary.consumed inbounds
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
          exact point.end_step ops law initialLocals bodyResults next advance inbounds out
            sourceBound bodyBound encoded isEnd accepted rest
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
