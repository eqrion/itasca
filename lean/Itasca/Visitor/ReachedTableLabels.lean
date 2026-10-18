import Itasca.Visitor.BrTableTrace
namespace Itasca
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The target collector only calls a visitor at the label states reached by
actual decoding. Its invariant may retain a growing visitor scratch buffer. -/
theorem code.read_table_labels_loop.total_on {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (count : U32) (inv : Nat → code.OpIterState → V → Prop)
    (callback : ∀ st v index depth target next,
      index < count.val → inv index st v →
      code.read_label st data = .ok (.Ok (depth,target),next) →
      visitor.on_br_table_label v next depth ⦃ out =>
        out.1 = .Ok () → inv (index+1) next out.2 ⦄)
    (st : code.OpIterState) (v : V) (expect : Option code.BlockType) (index : U32)
    (bound : index.val ≤ count.val) (initial : inv index.val st v) :
    code.read_table_labels_loop visitor st data count v expect index ⦃ out =>
      ∀ common, out.1 = .Ok common → inv count.val out.2.1 out.2.2 ⦄ := by
  generalize measure : count.val-index.val = n
  induction n using Nat.strong_induction_on generalizing st v expect index with
  | h n ih =>
    unfold code.read_table_labels_loop
    rw [loop]
    simp only [code.read_table_labels_loop.body]
    by_cases finished : index = count
    · simp [finished,WP.spec_ok]
      simpa only [finished] using initial
    · have inside : index.val < count.val := by
        have ne : index.val ≠ count.val := fun same => finished (UScalar.eq_of_val_eq same)
        omega
      simp only [finished,↓reduceIte]
      obtain ⟨⟨read,next⟩,readCall,_⟩ := WP.spec_imp_exists (code.read_label.spec st data)
      rw [readCall]
      cases read with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨depth,target⟩ := pair
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
        obtain ⟨⟨reply,middle⟩,called,held⟩ := WP.spec_imp_exists
          (callback st v index.val depth target next inside initial readCall)
        rw [called]
        cases reply with
        | Err error => simp [code.visit,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok unit =>
          cases unit
          obtain ⟨bt,btCall,_⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
          obtain ⟨merged,mergeCall,mergePost⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
          simp only [code.visit,bind_ok,core.result.Result.Insts.CoreOpsTry.branch,btCall,mergeCall,Std.uncurry]
          cases merged with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok result =>
            obtain ⟨resultEq,_⟩ := mergePost result rfl
            subst result
            obtain ⟨nextIndex,increment,nextEq⟩ := WP.spec_imp_exists
              (UScalar.add_spec (x:=index) (y:=1#u32) (by scalar_tac))
            simp only [increment,bind_ok]
            have fresh := held rfl
            have indexEq : nextIndex.val=index.val+1 := by simpa using nextEq
            have recursive := ih (count.val-nextIndex.val) (by omega) next middle (some bt) nextIndex
              (by omega) (by simpa only [indexEq] using fresh) rfl
            simpa only [code.read_table_labels_loop,code.read_table_labels_loop.body,code.visit,core.result.Result.Insts.CoreOpsTry.branch,Std.uncurry] using recursive
end Itasca
