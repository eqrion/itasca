import Exec.Code.Body.Control.Calls.CumulativePointIndirectCall
import Exec.Code.Body.Control.Common.CumulativePointNumeric
import Exec.Code.Body.Control.Common.CumulativePointOrdinary
import Exec.Code.Body.Control.Control.CumulativePointControl
import Exec.Code.Body.Control.Common.CumulativePointRoot
import Exec.Code.Body.Control.Common.CumulativePointExtra
import Exec.Code.Body.Control.Common.CumulativePointStateful
import Exec.Code.Local.Control.Common.CumulativeMiscSupport
import Exec.Code.Local.Control.Common.CumulativeOpcodes
import Exec.Code.Body.Reader.Common.ReaderOpcodePartition
import Exec.Code.Body.Reader.Common.ReaderCompilerBounds
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
private theorem fold_cumulative_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A)
    (C : context)
    (initial : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (ft : Itasca.types.FuncType) (source : List instr)
    (progress : ∀ (st : code.BodyState) (before middle final : runtime.compiler.FunctionCompiler A)
      (next : Usize) (out : code.BodyState),
      CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st →
      next.val = st.core.pos.val + 1 →
      (inbounds : st.core.pos.val < data.length) →
      code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {core := {st.core with pos := next}} data env ctx index .Wasm2
        data.val[st.core.pos.val] before = .ok (.Ok (), out, middle) →
      TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out middle final →
      StructuredCompiledBody (CumulativeEmission final.function.indirect.val C) initial final types functions returns locals source ∨
      CumulativeReaderCompilerPointWasm2 C initial middle types functions returns locals data env ctx.locals index ft out)
    {st before final}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : CumulativeReaderCompilerPointWasm2 C initial before types functions returns locals data env ctx.locals index ft st) :
    StructuredCompiledBody (CumulativeEmission final.function.indirect.val C) initial final types functions returns locals source := by
  induction run with
  | done typed closed finished =>
    obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point []
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


/-- Successful validation of a cumulative body constructs its contextual code
relation against the final, actually accumulated function-local pair table. -/
theorem TypedRunWasm2.compile_cumulative {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st source}
    (C : context)
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : CumulativeReaderCompilerPointWasm2 C initial before (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (encoded : Wasm2.BodyEncoding data source) (supported : Forall Abs.CumulativeInstr source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    StructuredCompiledBody (CumulativeEmission final.function.indirect.val C) initial final
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals source := by
  apply fold_cumulative_wasm2 ops C initial _ _ _ _ data env ctx index ft source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point []
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := encoded.next_cumulative_opcode supported state.boundary.consumed inbounds
  rcases allowed with floatCore | stateful | indirect
  · rcases floatCore with core | floatBase | prefixed
    · rcases core with allowed | extra
      · rcases allowed.partition with ordinary | scope | isElse | isEnd
        · exact .inr (point.ordinary ops law contextLocals metadata localsMatch next advance inbounds out sourceBound bodyBound
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
      · exact .inr (point.core_extra ops law C contextLocals matched.globals matched.mems
          next advance inbounds out sourceBound bodyBound _ extra rfl accepted)
    · obtain ⟨op,baseOpcode,equal⟩ := float_base_opcode_of_mem floatBase
      rw [← equal] at accepted
      exact .inr (point.float_base ops law contextLocals next advance inbounds out op baseOpcode sourceBound bodyBound equal.symm accepted)
    · obtain ⟨subopcode,endPosition,decoded,choice⟩ :=
        encoded.next_cumulative_misc supported state.boundary.consumed inbounds next advance prefixed
      rw [prefixed] at accepted
      rcases choice with ⟨op,extension,subopcodeEq⟩ | bulk
      · exact .inr (point.float_saturating ops law contextLocals next advance inbounds out op extension
          subopcode endPosition subopcodeEq decoded sourceBound bodyBound prefixed accepted)
      · exact .inr (point.stateful_bulk ops law matched contextLocals next advance inbounds out subopcode endPosition bulk
          sourceBound bodyBound prefixed decoded accepted)
  · exact .inr (point.stateful_base ops law matched contextLocals next advance inbounds out _ stateful
      sourceBound bodyBound rfl accepted)
  · rw [indirect] at accepted
    exact .inr (point.indirect_call_with ops law (fun _ _ _ _ _ head => .indirect head)
      matched contextLocals signatures next advance inbounds out sourceBound bodyBound indirect accepted)
end Exec.Code
