import Exec.Code.Body.Reader.Table.TableReaderCompilerFold
import Exec.Code.Body.Relations.Table.TablePointIndirectCall
import Exec.Code.Body.Relations.Table.TablePointNumeric
import Exec.Code.Body.Relations.Table.TablePointOrdinary
import Exec.Code.Body.Relations.Table.TablePointControl
import Exec.Code.Body.Relations.Table.TablePointRoot
import Exec.Code.Body.Relations.Table.TablePointExtra
import Exec.Code.Body.Reader.Table.TableReaderCompilerStateful
import Exec.Code.Body.Reader.Simd.TableReaderCompilerSimd
import Exec.Code.Local.Lowering.Simd.SimdCumulativeOpcodes
import Exec.Code.Local.Relations.Common.BodyEncodingMisc
import Exec.Code.Body.Reader.Common.ReaderOpcodePartition
import Exec.Code.Body.Reader.Common.ReaderCompilerBounds
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
/-- Successful validation of a cumulative body constructs its contextual code
relation against the final, actually accumulated function-local pair table. -/
theorem TypedRunWasm2.compile_simd_cumulative {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st source}
    (C : context)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (includeSimd : ∀ tables, SimdEmbedding tables.simd tables.constants C (emit tables))
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : TableReaderCompilerPointWasm2 emit initial before (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (encoded : Wasm2.BodyEncoding data source) (supported : Forall Abs.SimdCumulativeInstr source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    StructuredCompiledBody (emit (CompilerTables.ofFunction final.function)) initial final
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals source := by
  apply TypedRunWasm2.fold_tables ops emit initial _ _ _ _ data env ctx index ft source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point CompilerTables.empty
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := encoded.next_simd_cumulative_opcode supported state.boundary.consumed inbounds
  rcases allowed with cumulative | simd
  · rcases cumulative with floatCore | stateful | indirect
    · rcases floatCore with core | floatBase | prefixed
      · rcases core with allowed | extra
        · rcases allowed.partition with ordinary | scope | isElse | isEnd
          · exact .inr (point.ordinary ops law contextLocals includeCumulative metadata localsMatch next advance inbounds out sourceBound bodyBound
              _ ordinary rfl accepted)
          · exact .inr (point.scope_step ops law next advance inbounds out sourceBound signatures _ scope rfl accepted)
          · rw [isElse] at accepted
            exact .inr (point.else_ ops law next advance inbounds out initialLocals
              (by simpa only [global_simps] using isElse) (by simpa only [global_simps] using accepted))
          · rw [isEnd] at accepted
            by_cases root : st.blocks.val.length = 1
            · exact .inl (point.finish_root ops law root next advance inbounds out sourceBound bodyBound encoded isEnd accepted rest)
            · exact .inr (point.end_nested ops law next advance inbounds out initialLocals rfl root bodyBound
                (by simpa only [global_simps] using isEnd) (by simpa only [global_simps] using accepted))
        · exact .inr (point.core_extra ops law C includeCumulative contextLocals matched.globals matched.mems
            next advance inbounds out sourceBound bodyBound _ extra rfl accepted)
      · obtain ⟨op,baseOpcode,equal⟩ := float_base_opcode_of_mem floatBase
        rw [← equal] at accepted
        exact .inr (point.float_base ops law includeCumulative contextLocals next advance inbounds out op baseOpcode sourceBound bodyBound equal.symm accepted)
      · obtain ⟨subopcode,endPosition,decoded,choice⟩ :=
          encoded.next_misc state.boundary.consumed inbounds next advance prefixed
        rw [prefixed] at accepted
        rcases choice with ⟨op,extension,subopcodeEq⟩ | bulk
        · exact .inr (point.float_saturating ops law includeCumulative contextLocals next advance inbounds out op extension
            subopcode endPosition subopcodeEq decoded sourceBound bodyBound prefixed accepted)
        · exact .inr (point.stateful_bulk ops law includeCumulative matched contextLocals next advance inbounds out subopcode endPosition bulk
            sourceBound bodyBound prefixed decoded accepted)
    · exact .inr (point.stateful_base ops law includeCumulative matched contextLocals next advance inbounds out _ stateful
        sourceBound bodyBound rfl accepted)
    · rw [indirect] at accepted
      exact .inr (point.indirect_call ops law includeCumulative
        matched contextLocals signatures next advance inbounds out sourceBound bodyBound indirect accepted)
  · rw [simd] at accepted
    exact .inr (point.simd ops law C contextLocals matched.mems includeSimd next advance inbounds out sourceBound bodyBound simd accepted)
end Exec.Code
