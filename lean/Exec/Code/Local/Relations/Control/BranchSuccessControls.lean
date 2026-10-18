import Exec.Code.Local.Relations.Control.ControlMapCounts
import Exec.Code.Local.Callbacks.Common.CompilerPatchMetadata
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
/-- Branch emission only changes instructions, frame fixups and operand metadata;
it never changes the structural control map, including on a normal rejection. -/
theorem compiler_branch_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' maps_step accepted using ops, law

theorem callback_branch_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (ty : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth ty = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  split at accepted
  · obtain ⟨⟨result, middle⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
    have kept := compiler_branch_controls_result ops law before middle depth 0#u32 false result branchCall
    cases result with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, rfl⟩ := rest
      exact kept
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      have observed := compiler_observe_ordinary_result ops law _ after state status rest
      exact observed.controls.trans kept
  · exact (compiler_observe_ordinary_result ops law before after state status accepted).controls

theorem callback_branch_if_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (ty : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth ty = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  split at accepted
  · obtain ⟨⟨result, middle⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
    have kept := compiler_branch_controls_result ops law before middle depth 1#u32 true result branchCall
    cases result with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, rfl⟩ := rest
      exact kept
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      have observed := compiler_observe_ordinary_result ops law middle after state status rest
      exact observed.controls.trans kept
  · exact (compiler_observe_ordinary_result ops law before after state status accepted).controls
end Exec.Code
