import Itasca.Runtime.Code.Body.Reader.Table.ReaderTableBody
import Itasca.Binary.Wasm1.EncodingComplete
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
