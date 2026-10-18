import Exec.Code.Body.Reader.Common.ReaderCompilerPoint
import Exec.Code.Body.Reader.Common.ReaderCompilerRoot
import Exec.Code.Body.Reader.Common.ReaderOpcodePartition
import Exec.Code.Body.Reader.Common.ReaderCompilerBounds
import Exec.Code.Body.Reader.Control.ReaderCompilerElse
import Exec.Code.Body.Reader.Common.ReaderCompilerEndWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem fold_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A)
    (initial : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (ft : Itasca.types.FuncType) (source : List instr)
    (progress : ∀ (st : code.BodyState) (before middle final : runtime.compiler.FunctionCompiler A)
      (next : Usize) (out : code.BodyState),
      ReaderCompilerPointWasm2 initial before types functions returns locals data env ctx.locals index ft st →
      next.val = st.core.pos.val + 1 →
      (inbounds : st.core.pos.val < data.length) →
      code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index .Wasm2
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) →
      TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out middle final →
      CompiledBody initial final types functions returns locals source ∨
      ReaderCompilerPointWasm2 initial middle types functions returns locals data env ctx.locals index ft out)
    {st before final}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : ReaderCompilerPointWasm2 initial before types functions returns locals data env ctx.locals index ft st) :
    CompiledBody initial final types functions returns locals source := by
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
theorem TypedRunWasm2.compile_slice {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st source}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : ReaderCompilerPointWasm2 initial before (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (encoded : Wasm2.BodyEncoding data source) (supported : Forall Abs.SliceInstr source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    CompiledBody initial final (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals source := by
  apply fold_wasm2 ops initial _ _ _ _ data env ctx index ft source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := (encoded.next_slice_opcode supported state.boundary.consumed inbounds).partition
  rcases allowed with ordinary | scope | isElse | isEnd
  · exact .inr (state.ordinary ops law metadata localsMatch next advance inbounds out sourceBound bodyBound
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
end Exec.Code
