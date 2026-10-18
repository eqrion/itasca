import Exec.Code.Body.Reader.Table.ReaderTableLabels
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Exact collecting-reader cutpoint for Wasm 1. Source coordinates describe the
vector and default immediates before the validator's stack-only adjustment. -/
theorem compiler_read_br_table_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.OpIterState) (data : Slice U8) (default : U32) (common : code.BlockType)
    (accepted : code.read_br_table (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data before = .ok (.Ok (default,common),final,after)) :
    ∃ (count : U32) (first defaultStart defaultEnd : Usize) (depths : List U32)
      (budget : runtime.compiler.Budget A) (buffer : alloc.vec.Vec U32),
      Leb128.Decoded data st.pos count first ∧
      BrTable.LabelsDecoded data first depths defaultStart ∧
      Leb128.Decoded data defaultStart default defaultEnd ∧
      depths.length = count.val ∧
      after = {before with budget,table_depths := buffer} ∧
      buffer.val = before.table_depths.val ++ depths := by
  obtain ⟨countRead,countCall,countSpec⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  unfold code.read_br_table at accepted
  rw [countCall] at accepted
  cases countRead with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨count,first⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch] at accepted
    obtain ⟨⟨labelsResult,labelsState,collected⟩,labelsCall,rest⟩ := bind_ok_inv _ _ _ accepted
    cases labelsResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok expect =>
      obtain ⟨depths,budget,buffer,collectedEq,bufferEq,decoded,countEq,_,_⟩ :=
        compiler_read_table_labels ops law before collected {st with pos := first} labelsState data count 0#u32 none expect
          (by scalar_tac) labelsCall
      obtain ⟨⟨defaultRead,defaultState⟩,defaultCall,_,_,defaultSpec⟩ := WP.spec_imp_exists (code.read_label.spec labelsState data)
      simp [defaultCall] at rest
      cases defaultRead with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok pair =>
        obtain ⟨fallback,target⟩ := pair
        obtain ⟨defaultDecoded,_,_⟩ := defaultSpec
        obtain ⟨bt,btCall,_⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
        obtain ⟨merged,mergeCall,_⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
        simp [btCall,mergeCall] at rest
        cases merged with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok result =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at rest
          obtain ⟨⟨popResult,popState⟩,_,rest⟩ := bind_ok_inv _ _ _ rest
          cases popResult with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok value =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at rest
            obtain ⟨types,_,rest⟩ := bind_ok_inv _ _ _ rest
            obtain ⟨⟨argsResult,argsState⟩,_,rest⟩ := bind_ok_inv _ _ _ rest
            cases argsResult with
            | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok unit =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at rest
              obtain ⟨marked,_,rest⟩ := bind_ok_inv _ _ _ rest
              simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at rest
              obtain ⟨⟨rfl,rfl⟩,rfl,rfl⟩ := rest
              exact ⟨count,first,labelsState.pos,defaultState.pos,depths,budget,buffer,
                countSpec,decoded,defaultDecoded,by simpa using countEq,collectedEq,bufferEq⟩
end Exec.Code
