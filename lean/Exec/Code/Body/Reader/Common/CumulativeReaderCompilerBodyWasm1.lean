import Exec.Code.Body.Control.Calls.CumulativePointIndirectCall
import Exec.Code.Body.Control.Common.CumulativeRootWasm1
import Exec.Code.Body.Reader.Calls.ReaderOrdinaryIndirectWasm1
import Exec.Code.Body.Reader.Calls.ReaderExtraIndirectWasm1
import Exec.Code.Body.Reader.Memory.ReaderMemoryMetadataIndirectWasm1
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
import Exec.Code.Local.Control.Common.CumulativeWasm1Opcodes
import Exec.Code.Body.Lowering.Float.FloatEmbedding
import Exec.Code.Body.Reader.Memory.StructuredReaderCompilerMemorySize
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem fold_cumulative_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A)
    (C : context)
    (initial : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bodyBt : code.BlockType)
    (source : List instr)
    (progress : ∀ (st : code.OpIterState) (before middle final : runtime.compiler.FunctionCompiler A)
      (next : Usize) (out : code.OpIterState),
      CumulativeReaderCompilerPointWasm1 C initial before types functions returns locals data env ctx bodyBt st →
      next.val = st.pos.val + 1 →
      (inbounds : st.pos.val < data.length) →
      code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        {st with pos := next} data env ctx
        data.val[st.pos.val] before = .ok (.Ok (), out, middle) →
      TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt out middle final →
      StructuredCompiledBody (CumulativeEmission final.function.indirect.val C) initial final types functions returns locals source ∨
      CumulativeReaderCompilerPointWasm1 C initial middle types functions returns locals data env ctx bodyBt out)
    {st before final}
    (run : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt st before final)
    (point : CumulativeReaderCompilerPointWasm1 C initial before types functions returns locals data env ctx bodyBt st) :
    StructuredCompiledBody (CumulativeEmission final.function.indirect.val C) initial final types functions returns locals source := by
  induction run with
  | done typed closed finished =>
    obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point []
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
theorem TypedRunWasm1.compile_cumulative {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx bodyBt st source}
    (C : context)
    (run : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt st before final)
    (point : CumulativeReaderCompilerPointWasm1 C initial before (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
    (encoded : Wasm1.BodyEncoding data source) (supported : Forall Abs.CumulativeInstr source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (contextLocals : C.LOCALS = locals)
    (matched : EnvTranslation.Matches env ctx C)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    StructuredCompiledBody (CumulativeEmission final.function.indirect.val C) initial final (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals source := by
  apply fold_cumulative_wasm1 ops C initial _ _ _ _ data env ctx bodyBt source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point []
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := (encoded.next_cumulative_wasm1_opcode supported state.boundary.consumed inbounds)
  rcases allowed with legacy | memory | indirect
  · rcases legacy with core | floatBase | prefixed
    · rcases core with allowed | extra
      · rcases allowed.partition with ordinary | scope | isElse | isEnd
        · apply Or.inr
          have pairs := reader_ordinary_indirect_wasm1 (state.boundary.pending next advance inbounds)
            ops law before middle out _ ordinary rfl accepted
          apply point.preserved_step pairs
          intro future old
          obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
          exact state.ordinary ops law (by intro input instruction code output h; apply CumulativeEmission.left; apply FloatCoreEmission.core; apply CoreEmission.pure; simpa only [contextLocals] using h) metadata localsMatch next advance inbounds out sourceBound bodyBound bodyResults
            _ ordinary rfl accepted
        · apply Or.inr
          have pairs := reader_scope_indirect_wasm1 (state.boundary.pending next advance inbounds)
            ops law before middle out _ scope rfl accepted
          apply point.preserved_step pairs
          intro future old
          exact old.scope_step ops law next advance inbounds out sourceBound _ scope rfl accepted
        · rw [isElse] at accepted
          apply Or.inr
          have pairs := reader_else_indirect_wasm1 (state.boundary.pending next advance inbounds)
            ops law before middle out isElse accepted
          apply point.preserved_step pairs
          intro future old
          obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
          exact state.else_ ops law initialLocals next advance inbounds out
            (by simpa only [global_simps] using isElse) (by simpa only [global_simps] using accepted)
        · rw [isEnd] at accepted
          have pairs := reader_end_indirect_wasm1 (state.boundary.pending next advance inbounds)
            ops law before middle out isEnd accepted
          by_cases closed : out.ctrls.val = []
          · have root : savedCurrent.form = .body := by
              by_contra notRoot
              have nextPoint := state.end_nested ops law initialLocals next advance inbounds out notRoot bodyBound
                (by simpa only [global_simps] using isEnd) (by simpa only [global_simps] using accepted)
              obtain ⟨_,_,_,_,nextState⟩ := nextPoint
              obtain ⟨_,_,_,_,_,_,controls,_⟩ := nextState.boundary.opened
              rw [closed] at controls
              simp at controls
            obtain ⟨rfl,rfl⟩ := state.root_scopes root
            have finalEq := state.root_end_final ops next advance inbounds out isEnd accepted rest
            subst final
            have complete := state.finish_root ops law root bodyResults next advance inbounds out
              sourceBound bodyBound encoded isEnd accepted rest
            exact .inl (by simpa only [pairs,List.append_nil] using complete)
          · apply Or.inr
            apply point.preserved_step pairs
            intro future old
            obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
            have root : savedCurrent.form ≠ .body := by
              intro root
              obtain ⟨rfl,rfl⟩ := state.root_scopes root
              let p := state.boundary.pending next advance inbounds
              obtain ⟨_,read,_,_,_,afterState⟩ := reader_end_wasm1 p
                (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before middle out
                (by simpa only [p,ReaderBoundaryWasm1.pending,global_simps] using isEnd) (by simpa only [global_simps] using accepted)
              obtain ⟨C,outer,spine,header,base,typed,controls,vals⟩ := state.boundary.opened
              have outerEq : outer = [] := by simpa using wasm1_spine_values spine
              have rawEq : st.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
              have effect := code.read_end.realizes {st with pos := next} [] savedCurrent.ctrl [] savedCurrent.vals
                (by simpa using controls) (by simp [rawEq]) (by simpa [outerEq] using base)
                (Nat.le_of_lt p.val_capacity)
              rw [read,WP.spec_ok] at effect
              exact closed effect.2.2.2.1
            exact state.end_nested ops law initialLocals next advance inbounds out root bodyBound
              (by simpa only [global_simps] using isEnd) (by simpa only [global_simps] using accepted)
      
      · apply Or.inr
        have pairs := reader_core_extra_indirect_wasm1 (state.boundary.pending next advance inbounds)
          ops law before middle out _ extra rfl accepted
        apply point.preserved_step pairs
        intro future old
        obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
        exact state.core_extra ops law C contextLocals matched.globals matched.mems
          next advance inbounds out sourceBound bodyBound _ extra rfl accepted
    · obtain ⟨op,baseOpcode,equal⟩ := float_base_opcode_of_mem floatBase
      rw [← equal] at accepted
      apply Or.inr
      have pairs := reader_float_base_indirect_wasm1 (state.boundary.pending next advance inbounds)
        ops law before middle out op baseOpcode equal.symm accepted
      apply point.preserved_step pairs
      intro future old
      obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
      obtain ⟨values,nextState⟩ := state.float_base ops law C contextLocals next advance inbounds out op baseOpcode sourceBound bodyBound equal.symm accepted
      exact nextState.point
    · rw [prefixed] at accepted
      exact False.elim (float_saturating_wasm1_impossible
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before middle
        {st with pos := next} out data env ctx accepted)
  · apply Or.inr
    have pairs := reader_memory_metadata_indirect_wasm1 (state.boundary.pending next advance inbounds)
      ops law before middle out _ memory rfl accepted
    apply point.preserved_step pairs
    intro future old
    exact old.memory_metadata ops law matched contextLocals next advance inbounds out
      _ memory sourceBound bodyBound rfl accepted

  · rw [indirect] at accepted
    exact .inr (point.indirect_call_with ops law (fun _ _ _ _ _ head => .indirect head)
      matched contextLocals signatures next advance inbounds out sourceBound bodyBound indirect accepted)
end Exec.Code
