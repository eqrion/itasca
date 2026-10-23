import Exec.Code.Local.Relations.Table.BranchTableCallback
import Exec.Code.Local.Capacity.ControlCapacity
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem compiler_table_branch_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]?=some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index=.ok (.Ok (),after)) :
    capacityMetadata after=capacityMetadata before := by
  obtain ⟨target,budget,table,_,_,called⟩ := compiler_table_branch_success ops law before after index depth lookup accepted
  exact compiler_branch_capacity ops law {before with budget,function:={before.function with jump_tables:=table}}
    after depth 1#u32 false called

theorem TableBranchRun.capacity {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    capacityMetadata after=capacityMetadata before := by
  induction run with
  | done => rfl
  | @cons before middle after index inside called rest ih =>
    exact ih.trans (compiler_table_branch_capacity ops law before middle index before.table_depths.val[index.val]
      (List.getElem?_eq_getElem inside) called)

theorem compiler_lower_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before=.ok (.Ok (),after)) :
    capacityMetadata after=capacityMetadata before := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after accepted
  have retained := run.capacity law
  obtain ⟨budget,code,sources,rfl,_,_⟩ := emission
  exact retained

theorem compiler_br_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    CapacityStep before after state := by
  by_cases live : before.reachable=true
  · obtain ⟨budget,depths,lowered,cleared,_,called,_,observed⟩ :=
      compiler_br_table_success ops law before after state fallback types live accepted
    have retained := compiler_lower_table_capacity ops law {before with budget,table_depths:=depths} lowered called
    have fields : lowered.function.local_slots=before.function.local_slots ∧
        lowered.function.slot_count=before.function.slot_count := by
      simpa only [capacityMetadata,Prod.mk.injEq] using retained
    have effect := compiler_observe_capacity_bound ops law {lowered with reachable:=false,table_depths:=cleared}
      after state (.Ok ()) observed
    exact ⟨effect.1.trans fields.1,by simpa only [fields.1,fields.2] using effect.2 rfl⟩
  · have dead := Bool.eq_false_iff.mpr live
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at accepted
    obtain ⟨⟨result,labeled⟩,called,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      obtain ⟨budget,depths,rfl,_⟩ := compiler_table_label_success ops law before labeled state fallback called
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,dead,Bool.false_eq_true,ite_false] at rest
      obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      have effect := compiler_observe_capacity_bound ops law {before with budget,table_depths:=cleared} after state (.Ok ())
        (by simpa only [dead] using observed)
      exact ⟨effect.1,effect.2 rfl⟩
end Exec.Code
