import Exec.Code.Body.Reader.Table.ReaderTableRest
import Exec.Code.Body.Reader.Table.ReaderTableLabels
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts Itasca.Wasm2.Visitor
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

 theorem table_label_bytes (before after : code.BodyState) (data : Slice U8)
    (depth : U32) (types : signature.ResultType)
    (accepted : code.read_label_info before data = .ok (.Ok (depth,types),after)) :
    after.core.vals = before.core.vals ∧ after.core.ctrls = before.core.ctrls ∧
    Leb128.Decoded data before.core.pos depth after.core.pos := by
  unfold code.read_label_info at accepted
  obtain ⟨read,readCall,readSpec⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data before.core.pos)
  rw [readCall] at accepted
  cases read with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨decoded,next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at accepted
    obtain ⟨label,_,rest⟩ := bind_ok_inv _ _ _ accepted
    cases label with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok ts =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Result.ok.injEq,
        Prod.mk.injEq,core.result.Result.Ok.injEq] at rest
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := rest
      exact ⟨rfl,rfl,readSpec⟩

theorem compiler_table_body_cont {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (next : code.OpIterState) (data : Slice U8) (env : module.Env)
    (count index nextIndex : U32) (arity nextArity : Option Usize)
    (accepted : tableBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env count st before arity index = .ok (.cont (next,after,nextArity,nextIndex))) :
    ∃ depth budget buffer,
      after = {before with budget,table_depths := buffer} ∧
      buffer.val = before.table_depths.val ++ [depth] ∧
      Leb128.Decoded data st.core.pos depth next.pos ∧
      next.vals = st.core.vals ∧ next.ctrls = st.core.ctrls ∧
      index ≠ count ∧ nextIndex.val = index.val+1 := by
  unfold tableBody at accepted
  obtain ⟨⟨read,s⟩,readCall,rest⟩ := bind_ok_inv _ _ _ accepted
  cases read with
  | Err error => simp at rest
  | Ok pair =>
    obtain ⟨depth,types⟩ := pair
    have bytes := table_label_bytes st s data depth types readCall
    simp only [uncurry_apply_pair] at rest
    by_cases isLast : index = count
    · simp only [isLast,bne_self_eq_false,Bool.false_eq_true,ite_false] at rest
      exact False.elim ((table_rest_cont _ s env count count depth types arity before after next nextArity nextIndex rest).2.2.1 rfl)
    · simp only [bne_iff_ne,if_pos isLast] at rest
      obtain ⟨⟨reply,middle⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp only [code.visit,bind_ok,uncurry_apply_pair] at rest
        obtain ⟨rfl,rfl,_,nextEq⟩ := table_rest_cont _ s env count index depth types arity middle after next nextArity nextIndex rest
        obtain ⟨budget,buffer,same,appended⟩ := compiler_table_label_success ops law before _ s.core depth callback
        exact ⟨depth,budget,buffer,same,appended,bytes.2.2,bytes.1,bytes.2.1,isLast,nextEq⟩

theorem compiler_table_body_done {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env)
    (count index : U32) (arity : Option Usize)
    (accepted : tableBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env count st before arity index = .ok (.done (.Ok (),final,after))) :
    ∃ (depth : U32) (types : signature.ResultType) (readState : code.BodyState),
      index = count ∧
      Leb128.Decoded data st.core.pos depth readState.core.pos ∧
      code.mark_unreachable readState.core = .ok final.core ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops before final.core depth types = .ok (.Ok (),after) := by
  unfold tableBody at accepted
  obtain ⟨⟨read,s⟩,readCall,rest⟩ := bind_ok_inv _ _ _ accepted
  cases read with
  | Err error => simp at rest
  | Ok pair =>
    obtain ⟨depth,types⟩ := pair
    have bytes := table_label_bytes st s data depth types readCall
    simp only [uncurry_apply_pair] at rest
    by_cases isLast : index = count
    · simp only [isLast,bne_self_eq_false,Bool.false_eq_true,ite_false] at rest
      obtain ⟨_,marked,callback⟩ := table_rest_done _ s final env count count depth types arity before after rest
      exact ⟨depth,types,s,isLast,bytes.2.2,marked,callback⟩
    · simp only [bne_iff_ne,if_pos isLast] at rest
      obtain ⟨⟨reply,middle⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp only [code.visit,bind_ok,uncurry_apply_pair] at rest
        exact False.elim (isLast (table_rest_done _ s final env count index depth types arity middle after rest).1)
end Exec.Code
