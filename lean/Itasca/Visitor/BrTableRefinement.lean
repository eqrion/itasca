import Itasca.Support.Result
import Itasca.Visitor.Refinement
import Itasca.Handler.BrTable

/-!
# Refinement of the `br_table` reader

Lifts a `VisitorTrace.Refines` relation between visitors to the label loop
`code.read_table_labels_loop`, the label reader `code.read_table_labels` and the full
`code.read_br_table`, so results and validator state agree on every normal return.
-/

open Aeneas Aeneas.Std

namespace Itasca

open VisitorTrace

/-- A refinement of hooks lifts to the `br_table` label loop, including a rejection by the hook
before the observed target is merged. -/
theorem code.read_table_labels_loop.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V) (w : W)
    (hrelated : related v w) (expect : Option code.BlockType) (i : U32)
    (hi : i.val ≤ count.val) (res : core.result.Result (Option code.BlockType) error.OpError)
    (st' : code.OpIterState) (v' : V)
    (h : code.read_table_labels_loop visitor st data count v expect i = .ok (res, st', v')) :
    ∃ w', code.read_table_labels_loop replacement st data count w expect i =
      .ok (res, st', w') ∧ related v' w' := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st v w expect i with
  | h n ih =>
    unfold code.read_table_labels_loop at h ⊢
    unfold loop at h ⊢
    simp only [code.read_table_labels_loop.body] at h ⊢
    by_cases heq : i = count
    · simp [heq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨w, by simp [heq], hrelated⟩
    · simp only [heq, ↓reduceIte] at h ⊢
      obtain ⟨⟨label, s⟩, hr, _, _, _⟩ := WP.spec_imp_exists (code.read_label.spec st data)
      rw [hr] at h ⊢
      cases label with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, rfl, hrelated⟩
      | Ok pair =>
        obtain ⟨depth, target⟩ := pair
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
        obtain ⟨⟨reply, v1⟩, hv, hout⟩ := ResultFacts.bind_ok_inv _ _ _ h
        obtain ⟨w1, hw, hrelated1⟩ := hrefines v w (.op s (.br_table_label depth))
          reply v1 hrelated hv
        change replacement.on_br_table_label w s depth = .ok (reply, w1) at hw
        rw [hw]
        cases reply with
        | Err e =>
          simp [code.visit,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout ⊢
          obtain ⟨rfl, rfl, rfl⟩ := hout
          exact ⟨rfl, rfl, hrelated1⟩
        | Ok u =>
          obtain ⟨bt, hbt, _⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
          obtain ⟨merged, hm, _⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
          cases merged with
          | Err e =>
            simp [code.visit, hbt, hm,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout ⊢
            obtain ⟨rfl, rfl, rfl⟩ := hout
            exact ⟨rfl, rfl, hrelated1⟩
          | Ok common =>
            have hlt : i.val < count.val := by
              have hne : i.val ≠ count.val := fun he => heq (UScalar.eq_of_val_eq he)
              omega
            obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
              (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
            simp [code.visit, hbt, hm, hj] at hout
            have htail : code.read_table_labels_loop visitor s data count v1 (some common) j =
                .ok (res, st', v') := by
              simpa [code.read_table_labels_loop, code.read_table_labels_loop.body,
                code.visit, core.result.Result.Insts.CoreOpsTry.branch] using hout
            obtain ⟨w2, hrec, hr2⟩ := ih (count.val - j.val) (by scalar_tac)
              s v1 w1 hrelated1 (some common) j (by scalar_tac) htail rfl
            refine ⟨w2, ?_, hr2⟩
            simp [code.visit, hbt, hm, hj]
            simpa [code.read_table_labels_loop, code.read_table_labels_loop.body,
              code.visit, core.result.Result.Insts.CoreOpsTry.branch] using hrec

/-- A refinement of hooks lifts to the public label reader `code.read_table_labels`. -/
theorem code.read_table_labels.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V) (w : W)
    (hrelated : related v w) (res : core.result.Result (Option code.BlockType) error.OpError)
    (st' : code.OpIterState) (v' : V)
    (h : code.read_table_labels visitor st data count v = .ok (res, st', v')) :
    ∃ w', code.read_table_labels replacement st data count w =
      .ok (res, st', w') ∧ related v' w' :=
  code.read_table_labels_loop.refines visitor replacement related hrefines st data count v w
    hrelated none 0#u32 (by scalar_tac) res st' v' h

/-- A refinement of hooks lifts to `code.read_br_table` on every normal return. Only the label
hooks are called, and the related states carry through. -/
theorem code.read_br_table.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result (U32 × code.BlockType) error.OpError)
    (st' : code.OpIterState) (v' : V)
    (h : code.read_br_table visitor st data v = .ok (res, st', v')) :
    ∃ w', code.read_br_table replacement st data w = .ok (res, st', w') ∧ related v' w' := by
  unfold code.read_br_table at h ⊢
  obtain ⟨countResult, hc, hout⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hc]
  cases countResult with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hout
    exact ⟨rfl, rfl, hrelated⟩
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hout ⊢
    obtain ⟨⟨labels, s1, v1⟩, hl, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
    obtain ⟨w1, hlift, hrelated1⟩ := code.read_table_labels.refines visitor replacement
      related hrefines {st with pos := next} data count v w hrelated labels s1 v1 hl
    rw [hlift]
    cases labels with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout ⊢
      obtain ⟨rfl, rfl, rfl⟩ := hout
      exact ⟨rfl, rfl, hrelated1⟩
    | Ok expect =>
      simp at hout ⊢
      obtain ⟨⟨label, s2⟩, hd, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
      rw [hd]
      cases label with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout ⊢
        obtain ⟨rfl, rfl, rfl⟩ := hout
        exact ⟨rfl, rfl, hrelated1⟩
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
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout ⊢
          obtain ⟨rfl, rfl, rfl⟩ := hout
          exact ⟨rfl, rfl, hrelated1⟩
        | Ok common =>
          simp at hout ⊢
          obtain ⟨⟨selector, s3⟩, hs, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
          rw [hs]
          cases selector with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout ⊢
            obtain ⟨rfl, rfl, rfl⟩ := hout
            exact ⟨rfl, rfl, hrelated1⟩
          | Ok t =>
            simp at hout ⊢
            obtain ⟨types, ht, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
            rw [ht]
            simp only [bind_ok]
            obtain ⟨⟨operands, s4⟩, hp, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
            rw [hp]
            cases operands with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout ⊢
              obtain ⟨rfl, rfl, rfl⟩ := hout
              exact ⟨rfl, rfl, hrelated1⟩
            | Ok u =>
              simp at hout ⊢
              obtain ⟨s5, hu, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
              rw [hu]
              simp at hout ⊢
              obtain ⟨rfl, rfl, rfl⟩ := hout
              exact ⟨rfl, rfl, hrelated1⟩

end Itasca
