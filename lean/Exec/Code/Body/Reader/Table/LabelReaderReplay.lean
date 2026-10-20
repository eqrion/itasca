import Exec.Code.Local.Capacity.ReaderAcceptance
import Itasca.Visitor.ReachedTableLabels

namespace Itasca
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Replay the complete streamed label collector against an independently
accepted reference. Only labels actually read and accepted on that run require
available target callbacks. The relation can track scratch and branch budgets. -/
theorem code.read_table_labels_loop.accepted_replay_on {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W) (data : Slice U8) (count : U32)
    (related : Nat → code.OpIterState → V → W → Prop)
    (callbacks : ∀ st v w index depth label next middle,
      index < count.val → related index st v w →
      code.read_label st data = .ok (.Ok (depth,label),next) →
      source.on_br_table_label v next depth = .ok (.Ok (),middle) →
      target.on_br_table_label w next depth ⦃ out =>
        out.1 = .Ok () ∧ related (index+1) next middle out.2 ⦄)
    (st final : code.OpIterState) (before after : V) (compiler : W)
    (expect common : Option code.BlockType) (index : U32) (bounded : index.val ≤ count.val)
    (initial : related index.val st before compiler)
    (reference : code.read_table_labels_loop source st data count before expect index =
      .ok (.Ok common,final,after)) :
    code.read_table_labels_loop target st data count compiler expect index ⦃ out =>
      out.1 = .Ok common ∧ out.2.1 = final ∧ related count.val final after out.2.2 ⦄ := by
  generalize measure : count.val-index.val = n
  induction n using Nat.strong_induction_on generalizing st before compiler expect index with
  | h n ih =>
    unfold code.read_table_labels_loop at reference ⊢
    rw [loop] at reference ⊢
    simp only [code.read_table_labels_loop.body] at reference ⊢
    by_cases finished : index = count
    · simp only [finished,↓reduceIte,bind_ok,Result.ok.injEq,Prod.mk.injEq,
        core.result.Result.Ok.injEq] at reference
      obtain ⟨rfl,rfl,rfl⟩ := reference
      simpa [finished] using initial
    · have inside : index.val < count.val := by
        have ne : index.val ≠ count.val := fun same => finished (UScalar.eq_of_val_eq same)
        omega
      simp only [finished,↓reduceIte] at reference ⊢
      obtain ⟨⟨read,next⟩,readCalled,_⟩ := WP.spec_imp_exists (code.read_label.spec st data)
      rw [readCalled] at reference ⊢
      cases read with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at reference
      | Ok pair =>
        obtain ⟨depth,label⟩ := pair
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,Std.bind_assoc] at reference ⊢
        obtain ⟨⟨reply,middle⟩,sourceCalled,tail⟩ := ResultFacts.bind_ok_inv _ _ _ reference
        cases reply with
        | Err error =>
          simp [code.visit,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
        | Ok unit =>
          cases unit
          obtain ⟨⟨reply,targetAfter⟩,targetCalled,accepted,held⟩ := WP.spec_imp_exists
            (callbacks st before compiler index.val depth label next middle inside initial readCalled sourceCalled)
          dsimp only at accepted held
          subst reply
          rw [targetCalled]
          obtain ⟨bt,btCalled,_⟩ := WP.spec_imp_exists (code.branch_target_bt.spec label)
          obtain ⟨merged,mergeCalled,mergePost⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
          simp only [code.visit,bind_ok,core.result.Result.Insts.CoreOpsTry.branch,btCalled,mergeCalled,Std.uncurry]
            at tail ⊢
          cases merged with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
          | Ok result =>
            obtain ⟨resultEq,_⟩ := mergePost result rfl
            subst result
            obtain ⟨nextIndex,increment,nextEq⟩ := WP.spec_imp_exists
              (UScalar.add_spec (x := index) (y := 1#u32) (by scalar_tac))
            simp only [increment,bind_ok] at tail ⊢
            have indexEq : nextIndex.val = index.val+1 := by simpa using nextEq
            have tail' : code.read_table_labels_loop source next data count middle (some bt) nextIndex =
                .ok (.Ok common,final,after) := by
              simpa [code.read_table_labels_loop,code.read_table_labels_loop.body,code.visit,
                core.result.Result.Insts.CoreOpsTry.branch,Std.uncurry,Std.bind_assoc] using tail
            have recursive := ih (count.val-nextIndex.val) (by omega) next middle targetAfter (some bt) nextIndex
              (by omega) (by simpa only [indexEq] using held) tail' rfl
            simpa [code.read_table_labels_loop,code.read_table_labels_loop.body,code.visit,
              core.result.Result.Insts.CoreOpsTry.branch,Std.uncurry,Std.bind_assoc] using recursive

end Itasca
