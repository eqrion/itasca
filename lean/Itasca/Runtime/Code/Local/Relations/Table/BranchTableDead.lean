import Itasca.Runtime.Code.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Code.Local.Callbacks.Table.CompilerTableBoundary
import Itasca.Runtime.Code.Local.Relations.Table.TableSources
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

/-- Unreachable table instructions still consume and clear their label buffer,
while leaving the entire code, relocation table and frame stack unchanged. -/
theorem compiler_br_table_dead_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (dead : before.reachable=false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    TableFixed before after ∧ after.function.code=before.function.code ∧
    after.function.jump_tables=before.function.jump_tables ∧ after.frames=before.frames ∧
    after.table_depths.val=[] ∧ after.reachable=false ∧
    SourceProgress before after ∧ after.next_source=state.pos := by
  have sources := compiler_br_table_sources ops law before after state fallback types accepted
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at accepted
  obtain ⟨⟨result,labeled⟩,labeledCall,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    obtain ⟨budget,depths,rfl,_⟩ := compiler_table_label_success ops law before labeled state fallback labeledCall
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,dead,Bool.false_eq_true,ite_false] at rest
    obtain ⟨cleared,clearCall,observed⟩ := bind_ok_inv _ _ _ rest
    have empty := runtime_clear depths
    rw [clearCall,WP.spec_ok] at empty
    have kept := compiler_observe_frame ops law {before with budget,table_depths := cleared} state
    have stable := compiler_observe_stable ops law {before with budget,table_depths := cleared} after state
      (by simpa only [dead] using observed)
    simp only [dead] at kept
    rw [observed,WP.spec_ok] at kept
    dsimp only [ObserveFrame] at kept
    refine ⟨?_,?_,?_,?_,?_,?_,sources⟩
    · refine ⟨⟨stable.metadata,stable.capacity⟩,?_,?_,?_,?_⟩ <;> rw [kept]
    · rw [kept]
    · rw [kept]
    · rw [kept]
    · rw [kept]
      exact empty
    · rw [kept]
end Itasca.Runtime.Code
