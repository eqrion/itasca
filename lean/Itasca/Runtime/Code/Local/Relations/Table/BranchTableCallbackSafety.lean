import Itasca.Runtime.Code.Local.Relations.Table.BranchTableLowerSafety
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem compiler_br_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (aligned : SourceAligned compiler)
    (depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (fallbackBound : fallback.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (room : compiler.function.code.val.length + 1 + 2*(compiler.table_depths.val.length+1) ≤ Usize.max)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops compiler state fallback types ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  obtain ⟨⟨status,labeled⟩,called,_⟩ := WP.spec_imp_exists
    (compiler_table_label_total ops law compiler state fallback (by omega))
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
  rw [called]
  simp only [bind_ok]
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    obtain ⟨budget,labels,rfl,labelsEq⟩ := compiler_table_label_success ops law compiler labeled state fallback called
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    split
    · step with compiler_lower_table_total ops law {compiler with budget,table_depths := labels}
        aligned (by
          intro depth member
          rw [labelsEq] at member
          rcases List.mem_append.mp member with member | member
          · exact depths depth member
          · simp only [List.mem_singleton] at member
            subst depth
            exact fallbackBound)
        fixups (by simpa only [labelsEq,List.length_append,List.length_singleton] using room)
        tables coordinate as ⟨status,lowered⟩
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step with runtime_clear lowered.table_depths as ⟨cleared,_⟩
        exact compiler_observe_stack ops law {lowered with reachable := false,table_depths := cleared} state
    · step with runtime_clear labels as ⟨cleared,_⟩
      exact compiler_observe_stack ops law {compiler with budget,table_depths := cleared} state
end Itasca.Runtime.Code
