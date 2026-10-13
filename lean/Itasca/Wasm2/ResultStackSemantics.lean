import Itasca.Wasm2.ResultStack
import Itasca.Handler.StackComplete

/-!
# Descriptor stack operations, semantics and totality

Semantic specs of `code.pop_results` and `code.push_results`. `code.pop_results.realizes` relates
a successful pop to the backward stack interpretation, `.complete` gives acceptance from
independent stack compatibility, and `.total` and `code.push_results.total` show that neither
panics or diverges on arbitrary descriptors and environments.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Descriptor pops preserve the backward stack interpretation, including
mixed concrete/`Bot` stacks and implicit operands at an unreachable base. -/
theorem code.pop_results.realizes (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (expected : List types.ValueType)
    (outer segment : List code.StackType)
    (hts : Wasm2.resolve env view = some expected)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_results st env view ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        (r.1 = .Ok () → ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
          Sequence.Realizes (Control.polymorphic st) segment
            (ts ++ expected.map Translate.valueType)) ⦄ := by
  cases view with
  | Empty =>
    simp [Wasm2.resolve] at hts
    subst expected
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, segment, hvals, le_refl _, by simp⟩
  | One t =>
    simp [Wasm2.resolve] at hts
    subst expected
    obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hl, ht⟩ := WP.spec_imp_exists
      (code.pop_with_type.realizes st outer segment t hvals hbase)
    cases res <;> simp [code.pop_results, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · exact ⟨hc, hp, rest, hv, hl, ht.2⟩
    · exact ⟨hc, hp, rest, hv, hl⟩
  | «Type» index part =>
    by_cases hi : index.val < env.types.val.length
    · cases part <;> simp [Wasm2.resolve, List.getElem?_eq_getElem hi] at hts
      all_goals subst expected
      all_goals unfold code.pop_results
      all_goals step
      all_goals split
      all_goals first | scalar_tac | skip
      all_goals step
      all_goals step with code.pop_types.realizes st outer segment _ hvals hbase
      all_goals simp_all [alloc.vec.Vec.deref]
      all_goals intro hok; simpa [hok] using r_post4
    · simp [Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

/-- Independent stack compatibility suffices for descriptor-pop acceptance. -/
theorem code.pop_results.complete (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (expected : List types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype)
    (hts : Wasm2.resolve env view = some expected)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ expected.map Translate.valueType)) :
    code.pop_results st env view ⦃ r =>
      r.1 = .Ok () ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        Sequence.Realizes (Control.polymorphic st) rest ts ⦄ := by
  cases view with
  | Empty =>
    simp [Wasm2.resolve] at hts
    subst expected
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, trivial, segment, hvals, le_refl _, by simpa using ht⟩
  | One t =>
    simp [Wasm2.resolve] at hts
    subst expected
    obtain ⟨v, s, rest, hr, hc, hp, hv, hl, _, ht'⟩ :=
      code.pop_with_type.complete st outer segment ts t hvals hbase (by simpa using ht)
    simpa [code.pop_results, hr, core.result.Result.Insts.CoreOpsTry.branch]
      using And.intro hc (And.intro hp ⟨rest, hv, hl, ht'⟩)
  | «Type» index part =>
    by_cases hi : index.val < env.types.val.length
    · cases part <;> simp [Wasm2.resolve, List.getElem?_eq_getElem hi] at hts
      all_goals subst expected
      all_goals unfold code.pop_results
      all_goals step
      all_goals split
      all_goals first | scalar_tac | skip
      all_goals step
      all_goals first
        | step with code.pop_types.complete st outer segment ts (alloc.vec.Vec.deref ft.params) hvals hbase (by simpa [alloc.vec.Vec.deref, ft_post, r_post] using ht)
        | step with code.pop_types.complete st outer segment ts (alloc.vec.Vec.deref ft.results) hvals hbase (by simpa [alloc.vec.Vec.deref, ft_post, r_post] using ht)
      all_goals simp_all
    · simp [Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

/-- No descriptor, including an invalid type index, can make a bounded pop
panic or diverge. Frame bounds are preserved even on rejection. -/
@[step]
theorem code.pop_results.total (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (hshape : Control.Shape st) :
    code.pop_results st env view ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
        r.2.vals.val.length ≤ st.vals.val.length ⦄ := by
  cases view with
  | Empty => simp [code.pop_results, hshape]
  | One t =>
    unfold code.pop_results
    step with code.pop_with_type.total st t hshape
    step*
  | «Type» index part =>
    unfold code.pop_results
    step
    split
    · simp [hshape]
    · cases part <;> step
      all_goals step with code.pop_types.total st _ hshape
      all_goals simp_all

/-- The explicit capacity guard makes descriptor pushes total for arbitrary
environments, including invalid descriptors and oversized stored signatures. -/
@[step]
theorem code.push_results.total (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (hshape : Control.Shape st) :
    code.push_results st env view ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      (r.1 = .Ok () → ∃ ts, Wasm2.resolve env view = some ts ∧
        r.2.vals.val = st.vals.val ++ ts.map code.StackType.Val) ⦄ := by
  obtain ⟨res, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases res with
  | Err e =>
    simp [code.push_results, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hshape]
  | Ok n =>
    obtain ⟨ts, hts, hn⟩ := hs
    by_cases hcap : st.vals.val.length + ts.length ≤ Usize.max
    · obtain ⟨⟨r, s⟩, hrun, hok, hv, hc, hp⟩ := WP.spec_imp_exists
        (code.push_results.spec st env view ts hts hcap)
      rw [hrun, WP.spec_ok]
      refine ⟨hshape.replace_operands hc ?_, hc, hp, fun _ => ⟨ts, hts, hv⟩⟩
      have hb := hshape.base_le
      simp only [hv, List.length_append, List.length_map]
      omega
    · unfold code.push_results
      rw [hr]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step
      split
      · simp [hshape]
      · scalar_tac

end Itasca
