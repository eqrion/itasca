import Itasca.Runtime.Code.Body.Reader.Table.ReaderTableLoop
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Accepted reader decomposition with exact decoded count/targets and
actual selector-pop/final-callback equations. No replacement visitor is assumed. -/
theorem compiler_read_br_table {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env profile before = .ok (.Ok (),final,after)) :
    ∃ (count : U32) (first : Usize) (selector : code.StackType) (popped : code.OpIterState)
      (depths : List U32) (default : U32) (types : signature.ResultType)
      (defaultStart : Usize) (readState : code.BodyState) (budget : runtime.compiler.Budget A)
      (buffer : alloc.vec.Vec U32),
      Leb128.Decoded data st.core.pos count first ∧
      code.pop_with_type {st.core with pos := first} .I32 = .ok (.Ok selector,popped) ∧
      buffer.val = before.table_depths.val ++ depths ∧
      BrTable.LabelsDecoded data popped.pos depths defaultStart ∧
      Leb128.Decoded data defaultStart default readState.core.pos ∧
      depths.length = count.val ∧
      code.mark_unreachable readState.core = .ok final.core ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops {before with budget,table_depths := buffer} final.core default types = .ok (.Ok (),after) := by
  unfold code.branch_table_with at accepted
  obtain ⟨read,readCall,readSpec⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  rw [readCall] at accepted
  cases read with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨count,first⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at accepted
    obtain ⟨⟨result,popped⟩,popCall,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok selector =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at rest
      obtain ⟨depths,default,types,defaultStart,readState,budget,buffer,bufferEq,
        decoded,defaultDecoded,countEq,marked,callback⟩ :=
        compiler_table_loop ops law before after ⟨popped⟩ final data env profile count 0#u32 none .Empty
          (by scalar_tac) rest
      exact ⟨count,first,selector,popped,depths,default,types,defaultStart,readState,budget,buffer,
        readSpec,popCall,bufferEq,decoded,defaultDecoded,by simpa using countEq,marked,callback⟩
end Itasca.Runtime.Code
