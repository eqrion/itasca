import Itasca.Runtime.Store.Invariant.CopyTypes

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem value_type_equal (a b : Itasca.types.ValueType) :
    types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b ⦃ equal => equal = true ↔ a = b ⦄ := by
  cases a <;> cases b <;> simp [
    Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

@[step] theorem same_func_type_loop (left right : alloc.vec.Vec Itasca.types.ValueType)
    (position : Usize) (same : Bool) (gate : Prop) (hlen : left.length = right.length)
    (hpos : position.val ≤ left.length)
    (hprefix : same = true ↔ gate ∧ left.val.take position.val = right.val.take position.val) :
    runtime.store.same_func_type_loop0 left right position same ⦃ answer => answer = true ↔ gate ∧ left = right ⦄ := by
  unfold runtime.store.same_func_type_loop0
  apply loop.spec_decr_nat (fun pair => left.length - pair.1.val)
    (fun pair => pair.1.val ≤ left.length ∧
      (pair.2 = true ↔ gate ∧ left.val.take pair.1.val = right.val.take pair.1.val))
  · intro pair hinv
    rcases pair with ⟨pos, same⟩
    rcases hinv with ⟨hpos, hprefix⟩
    unfold runtime.store.same_func_type_loop0.body
    dsimp only at hpos hprefix ⊢
    split
    · rename_i hmore
      have hi : pos.val < left.length := by scalar_tac
      have hi' : pos.val < right.length := by omega
      cases same
      · simp
        intro hgate heq
        subst right
        simp [hgate] at hprefix
      · simp
        have hp : left.val.take pos.val = right.val.take pos.val := (hprefix.mp rfl).2
        have hg := (hprefix.mp rfl).1
        step as ⟨a, ha⟩
        step as ⟨b, hb⟩
        step with value_type_equal a b as ⟨equal, hequal⟩
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hnext, List.take_succ_eq_append_getElem hi, List.take_succ_eq_append_getElem hi', hp]
        simpa only [hg, true_and, ha, hb, List.append_cancel_left_eq, List.singleton_inj] using hequal
    · rename_i hstop
      have hend : pos.val = left.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [hend] at hprefix
      simp only [alloc.vec.Vec.length, List.take_length] at hprefix
      have hr : right.val.take left.val.length = right.val := by simpa [hlen] using List.take_length right.val
      rw [hr] at hprefix
      constructor
      · intro ht
        exact ⟨(hprefix.mp ht).1, alloc.vec.Vec.ext _ _ (hprefix.mp ht).2⟩
      · intro heq
        exact hprefix.mpr ⟨heq.1, congrArg alloc.vec.Vec.val heq.2⟩
  · exact ⟨hpos, hprefix⟩

@[step] theorem same_func_results_loop (left right : alloc.vec.Vec Itasca.types.ValueType)
    (position : Usize) (same : Bool) (gate : Prop) (hlen : left.length = right.length)
    (hpos : position.val ≤ left.length)
    (hprefix : same = true ↔ gate ∧ left.val.take position.val = right.val.take position.val) :
    runtime.store.same_func_type_loop1 left right position same ⦃ answer => answer = true ↔ gate ∧ left = right ⦄ := by
  have heq : runtime.store.same_func_type_loop1 left right position same =
      runtime.store.same_func_type_loop0 left right position same := by rfl
  rw [heq]
  exact same_func_type_loop left right position same gate hlen hpos hprefix

/-- The actual canonical-signature comparison is total and recognizes exact
parameter and result equality. -/
@[step] theorem same_func_type_spec (left right : Itasca.types.FuncType) :
    runtime.store.same_func_type left right ⦃ answer => answer = true ↔ left = right ⦄ := by
  unfold runtime.store.same_func_type
  dsimp only
  split
  · rename_i hne
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro heq
    subst right
    simp at hne
  · rename_i hparams
    split
    · rename_i hne
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
      intro heq
      subst right
      simp at hne
    · rename_i hresults
      have hp : left.params.length = right.params.length := by scalar_tac
      have hr : left.results.length = right.results.length := by scalar_tac
      step with same_func_type_loop left.params right.params 0#usize true True hp
        (by scalar_tac) (by simp) as ⟨same, hsame⟩
      step with same_func_results_loop left.results right.results 0#usize same
        (left.params = right.params) hr (by scalar_tac) (by simpa using hsame) as ⟨answer, hanswer⟩
      rw [hanswer]
      cases left
      cases right
      simp

theorem sourceType_injective : Function.Injective Interp.sourceType := by
  intro a b heq
  cases a <;> cases b <;> simp_all [Interp.sourceType]

theorem decodeFuncType_injective : Function.Injective decodeFuncType := by
  intro a b heq
  cases a with
  | mk ap ar =>
    cases b with
    | mk bp br =>
      simp only [decodeFuncType, functype.mk_functype.injEq, list.mk_list.injEq] at heq
      have hp := List.map_injective_iff.mpr sourceType_injective heq.1
      have hr := List.map_injective_iff.mpr sourceType_injective heq.2
      have hp' := alloc.vec.Vec.ext ap bp hp
      have hr' := alloc.vec.Vec.ext ar br hr
      cases hp'
      cases hr'
      rfl

end Itasca.Runtime.Store
