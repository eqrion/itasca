import Itasca.Support.Result
import Itasca.Body.BrTable
import Itasca.Visitor.VisitorErasure

open Aeneas Aeneas.Std

namespace Itasca

/-- Successful label iteration can erase its visitor without assuming that the visitor always terminates. -/
theorem code.read_table_labels_loop.accepted_erasure {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V)
    (expect : Option code.BlockType) (i : U32) (hi : i.val ≤ count.val)
    (result : Option code.BlockType) (st' : code.OpIterState) (v' : V)
    (h : code.read_table_labels_loop visitor st data count v expect i = .ok (.Ok result, st', v')) :
    code.read_table_labels_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data count () expect i =
      .ok (.Ok result, st', ()) := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st v expect i with
  | h n ih =>
    unfold code.read_table_labels_loop at h ⊢
    unfold loop at h ⊢
    simp only [code.read_table_labels_loop.body] at h ⊢
    by_cases heq : i = count
    · simp [heq] at h ⊢
      obtain ⟨rfl, rfl, _⟩ := h
      simp
    · simp only [heq, ↓reduceIte] at h ⊢
      obtain ⟨⟨res, s⟩, hr, _, _, _⟩ := WP.spec_imp_exists (code.read_label.spec st data)
      rw [hr] at h ⊢
      cases res with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨depth, target⟩ := pair
        simp [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc] at h ⊢
        obtain ⟨⟨vis, v1⟩, hv, hout⟩ := ResultFacts.bind_ok_inv _ _ _ h
        cases vis with
        | Err e =>
          simp [code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
        | Ok u =>
          cases u
          obtain ⟨bt, hbt, _⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
          obtain ⟨merged, hm, _⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
          cases merged with
          | Err e =>
            simp [code.visit, hbt, hm, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
          | Ok common =>
            have hlt : i.val < count.val := by
              have hne : i.val ≠ count.val := fun he => heq (UScalar.eq_of_val_eq he)
              omega
            obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
              (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
            simp [code.visit, hbt, hm, hj] at hout
            simp [code.OpVisitor.on_br_table_label.default,
              code.visit, hbt, hm, hj]
            have hrec := ih (count.val - j.val) (by scalar_tac) s v1 (some common) j (by scalar_tac) hout rfl
            simpa [code.read_table_labels_loop, code.read_table_labels_loop.body,
              code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor, code.OpVisitor.on_br_table_label.default,
              code.visit, core.result.Result.Insts.CoreOpsTry.branch] using hrec

/-- The public label reader starts the erasure induction at counter zero. -/
theorem code.read_table_labels.accepted_erasure {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V)
    (result : Option code.BlockType) (st' : code.OpIterState) (v' : V)
    (h : code.read_table_labels visitor st data count v = .ok (.Ok result, st', v')) :
    code.read_table_labels code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data count () =
      .ok (.Ok result, st', ()) :=
  code.read_table_labels_loop.accepted_erasure visitor st data count v none 0#u32
    (by scalar_tac) result st' v' h

end Itasca

namespace Itasca

/-- Accepting branch-table validation is independent of its label visitor. -/
theorem code.read_br_table.accepted_erasure {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (v : V)
    (result : U32 × code.BlockType) (st' : code.OpIterState) (v' : V)
    (h : code.read_br_table visitor st data v = .ok (.Ok result, st', v')) :
    code.read_br_table code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data () =
      .ok (.Ok result, st', ()) := by
  unfold code.read_br_table at h ⊢
  obtain ⟨countResult, hc, hout⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hc]
  cases countResult with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hout ⊢
    obtain ⟨⟨labels, s1, v1⟩, hl, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
    cases labels with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
    | Ok expect =>
      have he := code.read_table_labels.accepted_erasure visitor { st with pos := next }
        data count v expect s1 v1 hl
      rw [he]
      simp at hout ⊢
      obtain ⟨⟨label, s2⟩, hd, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
      rw [hd]
      cases label with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
      | Ok pair =>
        obtain ⟨default, target⟩ := pair
        simp at hout ⊢
        obtain ⟨bt, hb, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
        rw [hb]
        simp only [bind_ok]
        obtain ⟨merged, hm, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
        rw [hm]
        cases merged with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
        | Ok common =>
          simp at hout ⊢
          obtain ⟨⟨selector, s3⟩, hs, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
          rw [hs]
          cases selector with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
          | Ok t =>
            simp at hout ⊢
            obtain ⟨types, ht, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
            rw [ht]
            simp only [bind_ok]
            obtain ⟨⟨operands, s4⟩, hp, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
            rw [hp]
            cases operands with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
            | Ok u =>
              simp at hout ⊢
              obtain ⟨s5, hu, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
              rw [hu]
              simp only [bind_ok]
              simp at hout
              obtain ⟨rfl, rfl, _⟩ := hout
              rfl

end Itasca
