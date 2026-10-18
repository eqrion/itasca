import Exec.Code.Local.Relations.Table.BranchTableCallback
import Itasca.Visitor.BrTableTrace
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The actual Wasm 1 label reader appends exactly the binary-decoded target
vector to the compiler's collection buffer. Every other compiler field except
its resource budget stays fixed during collection. -/
theorem compiler_read_table_labels {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.OpIterState) (data : Slice U8) (count index : U32)
    (expect common : Option code.BlockType) (indexBound : index.val ≤ count.val)
    (accepted : code.read_table_labels_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data count before expect index = .ok (.Ok common,final,after)) :
    ∃ depths budget buffer,
      after = {before with budget,table_depths := buffer} ∧
      buffer.val = before.table_depths.val ++ depths ∧
      BrTable.LabelsDecoded data st.pos depths final.pos ∧
      index.val + depths.length = count.val ∧
      final.vals = st.vals ∧ final.ctrls = st.ctrls := by
  generalize measure : count.val - index.val = n
  induction n using Nat.strong_induction_on generalizing st index before expect with
  | h n ih =>
    unfold code.read_table_labels_loop at accepted
    rw [loop] at accepted
    simp only [code.read_table_labels_loop.body] at accepted
    by_cases finished : index = count
    · simp [finished] at accepted
      obtain ⟨rfl,rfl,rfl⟩ := accepted
      exact ⟨[],before.budget,before.table_depths,rfl,by simp,.nil,by simp [finished],rfl,rfl⟩
    · have inside : index.val < count.val := by
        have ne : index.val ≠ count.val := fun same => finished (UScalar.eq_of_val_eq same)
        omega
      simp only [finished,↓reduceIte] at accepted
      obtain ⟨⟨read,s⟩,readCall,values,controls,readPost⟩ := WP.spec_imp_exists (code.read_label.spec st data)
      dsimp only at values controls readPost
      rw [readCall] at accepted
      cases read with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok pair =>
        obtain ⟨depth,target⟩ := pair
        obtain ⟨decoded,depthBound,targetEq⟩ := readPost
        simp [core.result.Result.Insts.CoreOpsTry.branch,Std.bind_assoc] at accepted
        obtain ⟨⟨reply,middle⟩,callback,tail⟩ := bind_ok_inv _ _ _ accepted
        cases reply with
        | Err error => simp [code.visit,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
        | Ok unit =>
          cases unit
          obtain ⟨budget,buffer,rfl,bufferEq⟩ :=
            compiler_table_label_success ops law before middle s depth callback
          obtain ⟨bt,btCall,btEq⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
          obtain ⟨merged,mergeCall,mergePost⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
          cases merged with
          | Err error => simp [code.visit,btCall,mergeCall,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
          | Ok result =>
            obtain ⟨resultEq,_⟩ := mergePost result rfl
            subst result
            obtain ⟨next,nextCall,nextEq⟩ := WP.spec_imp_exists
              (UScalar.add_spec (x := index) (y := 1#u32) (by scalar_tac))
            simp [code.visit,btCall,mergeCall,nextCall] at tail
            have recursive : code.read_table_labels_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
                s data count {before with budget,table_depths := buffer} (some bt) next =
                .ok (.Ok common,final,after) := by
              simpa [code.read_table_labels_loop,code.read_table_labels_loop.body,code.visit,
                core.result.Result.Insts.CoreOpsTry.branch] using tail
            obtain ⟨depths,nextBudget,nextBuffer,afterEq,appendEq,remaining,countEq,finalValues,finalControls⟩ :=
              ih (count.val-next.val) (by scalar_tac) (before := _) (st := s) (index := next) (expect := some bt) (by scalar_tac) recursive rfl
            refine ⟨depth::depths,nextBudget,nextBuffer,afterEq,?_,?_,?_,finalValues.trans values,finalControls.trans controls⟩
            · simpa only [bufferEq,List.append_assoc,List.singleton_append] using appendEq
            · exact (BrTable.LabelsDecoded.snoc .nil decoded).append remaining
            · simp only [List.length_cons]
              scalar_tac
end Exec.Code
