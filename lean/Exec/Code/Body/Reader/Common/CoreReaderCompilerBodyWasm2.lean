import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerRoot
import Exec.Code.Body.Reader.Common.ReaderOpcodePartition
import Exec.Code.Body.Reader.Common.ReaderCompilerBounds
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerElse
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerEndWasm2
import Exec.Code.Local.Relations.Common.CoreOpcodes
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerExtra
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerOrdinary
import Exec.Code.Body.Reader.Control.StructuredReaderCompilerScopes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem fold_core_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (initial : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (ft : Itasca.types.FuncType) (source : List instr)
    (progress : ∀ (st : code.BodyState) (before middle final : runtime.compiler.FunctionCompiler A)
      (next : Usize) (out : code.BodyState),
      StructuredReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st →
      next.val = st.core.pos.val + 1 →
      (inbounds : st.core.pos.val < data.length) →
      code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index .Wasm2
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) →
      TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out middle final →
      StructuredCompiledBody emit initial final types functions returns locals source ∨
      StructuredReaderCompilerPointWasm2 emit initial middle types functions returns locals data env ctx.locals index ft out)
    {st before final}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : StructuredReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st) :
    StructuredCompiledBody emit initial final types functions returns locals source := by
  induction run with
  | done typed closed finished =>
    obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
    obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := state.boundary.opened
    rw [closed] at blocks
    simp at blocks
  | @step st before next out middle final typed pending start advance called rest ih =>
    have inbounds : st.core.pos.val < data.length := by simpa only [start] using pending.inbounds
    have called' : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index .Wasm2
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) := by
      simpa only [start] using called
    rcases progress st before middle final next out point advance inbounds called' rest with done | nextPoint
    · exact done
    · exact ih nextPoint

/-- A successful actual validation run of the supported source slice constructs
its emitted-code relation. Every reader case is derived from its actual
callback equation; no compiler-correctness premise is supplied. -/
theorem TypedRunWasm2.compile_core {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st source}
    (C : context)
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : StructuredReaderCompilerPointWasm2 (CoreEmission C) initial before (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (encoded : Wasm2.BodyEncoding data source) (supported : Forall Abs.CoreInstr source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (contextLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    StructuredCompiledBody (CoreEmission C) initial final (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals source := by
  apply fold_core_wasm2 ops (CoreEmission C) initial _ _ _ _ data env ctx index ft source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := (encoded.next_core_opcode supported state.boundary.consumed inbounds)
  rcases allowed with allowed | extra
  · rcases allowed.partition with ordinary | scope | isElse | isEnd
    · exact .inr (state.ordinary ops law (by intro input instruction code output h; apply CoreEmission.pure; simpa only [contextLocals] using h) metadata localsMatch next advance inbounds out sourceBound bodyBound
        _ ordinary rfl accepted)
    · exact .inr (state.point.scope_step ops law next advance inbounds out sourceBound signatures
        _ scope rfl accepted)
    · rw [isElse] at accepted
      exact .inr (state.else_ ops law initialLocals next advance inbounds out (by simpa only [global_simps] using isElse) (by simpa only [global_simps] using accepted))
    · rw [isEnd] at accepted
      by_cases root : savedCurrent.form = .body
      · obtain ⟨rfl, rfl⟩ := state.root_scopes root
        exact .inl (state.finish_root ops law root next advance inbounds out
          sourceBound bodyBound encoded isEnd accepted rest)
      · exact .inr (state.end_nested ops law initialLocals rfl next advance inbounds out root bodyBound
        (by simpa only [global_simps] using isEnd) (by simpa only [global_simps] using accepted))
  · exact .inr (state.core_extra ops law C contextLocals contextGlobals contextMemories
      next advance inbounds out sourceBound bodyBound _ extra rfl accepted)
end Exec.Code
