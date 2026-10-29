import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallback
import Itasca.Wasm2.Visitor.BrTable
import Itasca.Binary.Leb128
import Itasca.Binary.Wasm1.EncodingComplete

/-!
br_table reader inversion through label-vector body and loop execution. The final theorem identifies the decoded branch-table source instruction.
-/

/-! ## Reader Table Rest -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts Itasca.Wasm2.Visitor

 theorem table_rest_cont {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (env : module.Env) (count index depth : U32)
    (types : signature.ResultType) (arity : Option Usize) (first : signature.ResultType)
    (before after : V) (next : code.OpIterState) (nextArity : Option Usize)
    (nextFirst : signature.ResultType) (nextIndex : U32)
    (accepted : tableRest visitor st env count index depth types arity first before =
      .ok (.cont (next,after,nextArity,nextFirst,nextIndex))) :
    next = st.core ∧ after = before ∧ nextFirst = first ∧ index ≠ count ∧
      nextIndex.val = index.val + 1 := by
  unfold tableRest at accepted
  obtain ⟨checked,_,rest⟩ := bind_ok_inv _ _ _ accepted
  cases checked with
  | Err error => simp at rest
  | Ok newArity =>
    by_cases final : index = count
    · simp only [final,ite_true] at rest
      obtain ⟨marked,_,rest⟩ := bind_ok_inv _ _ _ rest
      obtain ⟨⟨reply,result⟩,_,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply <;> simp [code.visit] at rest
    · simp only [final,ite_false] at rest
      obtain ⟨incremented,increment,rest⟩ := bind_ok_inv _ _ _ rest
      simp only [Result.ok.injEq,ControlFlow.cont.injEq,Prod.mk.injEq] at rest
      obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := rest
      have arithmetic := UScalar.add_equiv index 1#u32
      rw [increment] at arithmetic
      exact ⟨rfl,rfl,rfl,final,by simpa using arithmetic.2.1⟩

theorem table_rest_done {V : Type} (visitor : code.OpVisitor V)
    (st final : code.BodyState) (env : module.Env) (count index depth : U32)
    (types : signature.ResultType) (arity : Option Usize) (first : signature.ResultType)
    (before after : V)
    (accepted : tableRest visitor st env count index depth types arity first before =
      .ok (.done (.Ok (),final,after))) :
    index = count ∧
    code.mark_unreachable st.core = .ok final.core ∧
    visitor.on_br_table before final.core depth types = .ok (.Ok (),after) := by
  unfold tableRest at accepted
  obtain ⟨checked,_,rest⟩ := bind_ok_inv _ _ _ accepted
  cases checked with
  | Err error => simp at rest
  | Ok newArity =>
    by_cases isLast : index = count
    · simp only [isLast,ite_true] at rest
      obtain ⟨marked,markedCall,rest⟩ := bind_ok_inv _ _ _ rest
      obtain ⟨⟨reply,result⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp [code.visit] at rest
        rcases rest with ⟨stateEq,visitorEq⟩
        cases final
        simp only [code.BodyState.mk.injEq] at stateEq
        subst after
        cases stateEq
        exact ⟨isLast,markedCall,callback⟩
    · simp only [isLast,ite_false] at rest
      obtain ⟨_,_,rest⟩ := bind_ok_inv _ _ _ rest
      simp at rest
end Itasca.Runtime.Code

end

/-! ## Reader Table Body -/

section

namespace Itasca.Runtime.Code
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
    (profile : ValidationProfile) (count index nextIndex : U32) (arity nextArity : Option Usize)
    (first nextFirst : signature.ResultType)
    (accepted : tableBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env profile count st before arity first index =
        .ok (.cont (next,after,nextArity,nextFirst,nextIndex))) :
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
    obtain ⟨checked,_,rest⟩ := bind_ok_inv _ _ _ rest
    cases checked with
    | Err error => simp at rest
    | Ok unit =>
    simp only [bind_ok] at rest
    by_cases isLast : index = count
    · simp only [isLast,bne_self_eq_false,Bool.false_eq_true,ite_false] at rest
      exact False.elim ((table_rest_cont _ s env count count depth types arity _ before after next
        nextArity nextFirst nextIndex rest).2.2.2.1 rfl)
    · simp only [bne_iff_ne,if_pos isLast] at rest
      obtain ⟨⟨reply,middle⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp only [code.visit,bind_ok,uncurry_apply_pair] at rest
        obtain ⟨rfl,rfl,_,_,nextEq⟩ := table_rest_cont _ s env count index depth types arity _ middle
          after next nextArity nextFirst nextIndex rest
        obtain ⟨budget,buffer,same,appended⟩ := compiler_table_label_success ops law before _ s.core depth callback
        exact ⟨depth,budget,buffer,same,appended,bytes.2.2,bytes.1,bytes.2.1,isLast,nextEq⟩

theorem compiler_table_body_done {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env)
    (profile : ValidationProfile) (count index : U32) (arity : Option Usize)
    (first : signature.ResultType)
    (accepted : tableBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env profile count st before arity first index = .ok (.done (.Ok (),final,after))) :
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
    obtain ⟨checked,_,rest⟩ := bind_ok_inv _ _ _ rest
    cases checked with
    | Err error => simp at rest
    | Ok unit =>
    simp only [bind_ok] at rest
    by_cases isLast : index = count
    · simp only [isLast,bne_self_eq_false,Bool.false_eq_true,ite_false] at rest
      obtain ⟨_,marked,callback⟩ := table_rest_done _ s final env count count depth types arity _
        before after rest
      exact ⟨depth,types,s,isLast,bytes.2.2,marked,callback⟩
    · simp only [bne_iff_ne,if_pos isLast] at rest
      obtain ⟨⟨reply,middle⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp only [code.visit,bind_ok,uncurry_apply_pair] at rest
        exact False.elim (isLast (table_rest_done _ s final env count index depth types arity _ middle
          after rest).1)
end Itasca.Runtime.Code

end

/-! ## Reader Table Loop -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts Itasca.Wasm2.Visitor
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The accepted target loop collects exactly its decoded nondefault
labels, then invokes the final callback once with the separately decoded default. -/
theorem compiler_table_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (count index : U32) (arity : Option Usize) (first : signature.ResultType)
    (indexBound : index.val ≤ count.val)
    (accepted : code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env profile before count arity first index = .ok (.Ok (),final,after)) :
    ∃ (depths : List U32) (default : U32) (types : signature.ResultType)
      (defaultStart : Usize) (readState : code.BodyState) (budget : runtime.compiler.Budget A)
      (buffer : alloc.vec.Vec U32),
      buffer.val = before.table_depths.val ++ depths ∧
      BrTable.LabelsDecoded data st.core.pos depths defaultStart ∧
      Leb128.Decoded data defaultStart default readState.core.pos ∧
      index.val + depths.length = count.val ∧
      code.mark_unreachable readState.core = .ok final.core ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops {before with budget,table_depths := buffer} final.core default types = .ok (.Ok (),after) := by
  generalize measure : count.val - index.val = n
  induction n using Nat.strong_induction_on generalizing before st index arity first with
  | h n ih =>
    unfold code.branch_table_with_loop at accepted
    rw [loop] at accepted
    simp only [tableBody_eq (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env profile count st before arity first index] at accepted
    obtain ⟨flow,bodyCall,tail⟩ := bind_ok_inv _ _ _ accepted
    cases flow with
    | done result =>
      obtain ⟨status,next,out⟩ := result
      simp only [Result.ok.injEq,Prod.mk.injEq] at tail
      obtain ⟨rfl,rfl,rfl⟩ := tail
      obtain ⟨default,types,readState,last,decoded,marked,callback⟩ :=
        compiler_table_body_done ops before _ st _ data env profile count index arity first bodyCall
      exact ⟨[],default,types,st.core.pos,readState,before.budget,before.table_depths,
        by simp,.nil,decoded,by simp [last],marked,callback⟩
    | cont next =>
      obtain ⟨nextState,middle,nextArity,nextFirst,nextIndex⟩ := next
      obtain ⟨depth,budget,buffer,rfl,appended,decoded,values,controls,nonLast,indexEq⟩ :=
        compiler_table_body_cont ops law before middle st nextState data env profile count index
          nextIndex arity nextArity first nextFirst bodyCall
      have nextBound : nextIndex.val ≤ count.val := by
        have ne : index.val ≠ count.val := fun same => nonLast (UScalar.eq_of_val_eq same)
        omega
      have recursive : code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
          nextState data env profile {before with budget,table_depths := buffer} count nextArity
            nextFirst nextIndex =
          .ok (.Ok (),final,after) := tail
      obtain ⟨depths,default,types,defaultStart,readState,nextBudget,nextBuffer,bufferEq,
        remaining,defaultDecoded,countEq,marked,callback⟩ :=
        ih (count.val-nextIndex.val) (by omega) (before := _) (st := ⟨nextState⟩)
          (index := nextIndex) (arity := nextArity) (first := nextFirst) nextBound recursive rfl
      refine ⟨depth::depths,default,types,defaultStart,readState,nextBudget,nextBuffer,?_,?_,
        defaultDecoded,?_,marked,callback⟩
      · simpa only [appended,List.append_assoc,List.singleton_append] using bufferEq
      · exact (BrTable.LabelsDecoded.snoc .nil decoded).append remaining
      · simp only [List.length_cons]
        omega
end Itasca.Runtime.Code

end

/-! ## Reader Table Wasm2 -/

section

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

end
