import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerRoot
import Exec.Code.Body.Reader.Common.ReaderOpcodePartition
import Exec.Code.Body.Reader.Common.ReaderCompilerBounds
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerElse
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerEndWasm1
import Exec.Code.Local.Lowering.Float.FloatCoreOpcodes
import Exec.Code.Local.Lowering.Float.FloatSaturatingSupport
import Exec.Code.Body.Lowering.Float.FloatLinearEmbedding
import Exec.Code.Body.Reader.Float.StructuredReaderCompilerFloat
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerSaturating
import Exec.Code.Body.Lowering.Float.FloatWasm1Exclusion
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerExtra
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerOrdinary
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerScopes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem fold_float_core_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (initial : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bodyBt : code.BlockType)
    (source : List instr)
    (progress : ∀ (st : code.OpIterState) (before middle final : runtime.compiler.FunctionCompiler A)
      (next : Usize) (out : code.OpIterState),
      StructuredReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st →
      next.val = st.pos.val + 1 →
      (inbounds : st.pos.val < data.length) →
      code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {st with pos := next} data env ctx
        data.val[st.pos.val] before = .ok (.Ok (), out, middle) →
      TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt out middle final →
      StructuredCompiledBody emit initial final types functions returns locals source ∨
      StructuredReaderCompilerPointWasm1 emit initial middle types functions returns locals data env ctx bodyBt out)
    {st before final}
    (run : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt st before final)
    (point : StructuredReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st) :
    StructuredCompiledBody emit initial final types functions returns locals source := by
  induction run with
  | done typed closed finished =>
    obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
    obtain ⟨_, _, _, _, _, _, controls, _⟩ := state.boundary.opened
    rw [closed] at controls
    simp at controls
  | @step st before next out middle final typed pending start advance called rest ih =>
    have inbounds : st.pos.val < data.length := by simpa only [start] using pending.inbounds
    have called' : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {st with pos := next} data env ctx
        data.val[st.pos.val] before = .ok (.Ok (), out, middle) := by
      simpa only [start] using called
    rcases progress st before middle final next out point advance inbounds called' rest with done | nextPoint
    · exact done
    · exact ih nextPoint

/-- A successful actual validation run of the supported source slice constructs
its emitted-code relation. Every reader case is derived from its actual
callback equation; no compiler-correctness premise is supplied. -/
theorem TypedRunWasm1.compile_float_core {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx bodyBt st source}
    (C : context)
    (run : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt st before final)
    (point : StructuredReaderCompilerPointWasm1 (FloatCoreEmission C) initial before (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
    (encoded : Wasm1.BodyEncoding data source) (supported : Forall Abs.FloatCoreInstr source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (contextLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    StructuredCompiledBody (FloatCoreEmission C) initial final (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals source := by
  apply fold_float_core_wasm1 ops (FloatCoreEmission C) initial _ _ _ _ data env ctx bodyBt source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := (encoded.next_float_core_opcode supported state.boundary.consumed inbounds)
  rcases allowed with core | floatBase | prefixed
  · rcases core with allowed | extra
    · rcases allowed.partition with ordinary | scope | isElse | isEnd
      · exact .inr (state.ordinary ops law (by intro input instruction code output h; apply FloatCoreEmission.core; apply CoreEmission.pure; simpa only [contextLocals] using h) metadata localsMatch next advance inbounds out sourceBound bodyBound bodyResults
          _ ordinary rfl accepted)
      · exact .inr (state.point.scope_step ops law next advance inbounds out sourceBound
          _ scope rfl accepted)
      · rw [isElse] at accepted
        exact .inr (state.else_ ops law initialLocals next advance inbounds out (by simpa only [global_simps] using isElse) (by simpa only [global_simps] using accepted))
      · rw [isEnd] at accepted
        by_cases root : savedCurrent.form = .body
        · obtain ⟨rfl, rfl⟩ := state.root_scopes root
          exact .inl (state.finish_root ops law root bodyResults next advance inbounds out
            sourceBound bodyBound encoded isEnd accepted rest)
        · exact .inr (state.end_nested ops law initialLocals next advance inbounds out root bodyBound
          (by simpa only [global_simps] using isEnd) (by simpa only [global_simps] using accepted))
    
    · exact .inr (state.core_extra ops law C contextLocals contextGlobals contextMemories
        next advance inbounds out sourceBound bodyBound _ extra rfl accepted)
  · obtain ⟨op,baseOpcode,equal⟩ := float_base_opcode_of_mem floatBase
    rw [← equal] at accepted
    obtain ⟨values,nextState⟩ := state.float_base ops law C contextLocals next advance inbounds out op baseOpcode sourceBound bodyBound equal.symm accepted
    exact .inr nextState.point
  · rw [prefixed] at accepted
    exact False.elim (float_saturating_wasm1_impossible
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before middle
      {st with pos := next} out data env ctx accepted)

end Exec.Code
