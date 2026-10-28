import Exec.Code.Body.Reader.Local.ReaderLocalEffects
import Exec.Code.Body.Reader.Common.ReaderBasic
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Successful local parsing checks the namespace before the compiler callback,
including unreachable stacks and without assuming successful compilation. -/
theorem reader_local_get_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_get st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_get,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_get,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨next,pushed,tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at tail
    obtain ⟨rfl,rfl⟩ := tail
    exact post.2.choose

theorem reader_local_set_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_set st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_set,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_set,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨⟨reply,next⟩,popped,tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok value =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at tail
      obtain ⟨rfl,rfl⟩ := tail
      exact post.2.choose

theorem reader_local_tee_bound (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (accepted : code.read_local_tee st data ctx = .ok (.Ok index,out)) :
    index.val < ctx.locals.val.length := by
  obtain ⟨⟨result,state⟩,read,values,controls,post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at post
  cases result with
  | Err error => simp [code.read_local_tee,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx,ty⟩ := pair
    simp only [code.read_local_tee,read,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at accepted
    obtain ⟨⟨reply,next⟩,popped,tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at tail
      obtain ⟨final,pushed,tail⟩ := ResultFacts.bind_ok_inv _ _ _ tail
      simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at tail
      obtain ⟨rfl,rfl⟩ := tail
      exact post.2.choose
end Itasca.Runtime.Code
