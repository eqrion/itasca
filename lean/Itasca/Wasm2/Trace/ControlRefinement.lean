import Itasca.Wasm2.Trace.Refinement
import Itasca.Wasm2.Visitor.Step

/-!
# Exact refinement of control dispatch

Exact visitor refinement for the `br_table` loop (`tableRest.refines`, `tableBody.refines`,
`code.branch_table_with_loop.refines`, `code.branch_table_with.refines`) and for the whole
`code.step_profile` (`code.step_profile.refines`), preserving computed signatures, partial tables
and callback rejection.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Wasm2.Visitor

open VisitorTrace

/-- The visitor state of one `br_table` iteration result. -/
def tableVisitor {V : Type} :
    ControlFlow (code.OpIterState × V × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V) → V
  | .cont (_, v, _, _, _) => v
  | .done (_, _, v) => v

/-- Exact visitor-state refinement through the suffix check and final table hook. -/
theorem tableRest.refines {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (related : V → W → Prop)
    (hrefines : Refines visitor replacement related)
    (st : code.BodyState) (env : metadata.Env) (count i depth : U32)
    (ts : signature.ResultType) (arity : Option Usize) (first : signature.ResultType)
    (v : V) (w : W) (hrelated : related v w) (cf)
    (h : tableRest visitor st env count i depth ts arity first v = .ok cf) :
    ∃ cf', tableRest replacement st env count i depth ts arity first w = .ok cf' ∧
      tableObserve cf' = tableObserve cf ∧ related (tableVisitor cf) (tableVisitor cf') := by
  unfold tableRest at h ⊢
  obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp only [ok.injEq] at h
    subst cf
    exact ⟨.done (.Err e, st, w), by simp, rfl, hrelated⟩
  | Ok nextArity =>
    simp only [bind_ok] at h ⊢
    by_cases he : i = count
    · simp only [he, if_true] at h ⊢
      obtain ⟨ois, ho, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rw [ho]
      simp only [bind_ok]
      obtain ⟨⟨reply, v'⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w', hw, hr'⟩ := hrefines v w (.op ois (.br_table depth ts)) reply v' hrelated hv
      change replacement.on_br_table w ois depth ts = .ok (reply, w') at hw
      rw [hw]
      cases reply <;> simp [code.visit] at h ⊢
      all_goals subst cf; exact ⟨rfl, hr'⟩
    · simp only [he, if_false] at h ⊢
      obtain ⟨j, hj, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      simp only [ok.injEq] at h
      subst cf
      exact ⟨.cont (st.core, w, nextArity, first, j), by simp [hj], rfl, hrelated⟩

/-- A table iteration includes every label callback, even the label whose later
type compatibility check fails. A rejecting callback remains last. -/
theorem tableBody.refines {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (related : V → W → Prop)
    (hrefines : Refines visitor replacement related)
    (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile) (count : U32)
    (st : code.BodyState) (v : V) (w : W) (hrelated : related v w) (arity : Option Usize)
    (first : signature.ResultType) (i : U32) (cf)
    (h : tableBody visitor data env profile count st v arity first i = .ok cf) :
    ∃ cf', tableBody replacement data env profile count st w arity first i = .ok cf' ∧
      tableObserve cf' = tableObserve cf ∧ related (tableVisitor cf) (tableVisitor cf') := by
  unfold tableBody at h ⊢
  obtain ⟨⟨r, s⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp at h
    subst cf
    exact ⟨.done (.Err e, s, w), by simp, rfl, hrelated⟩
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [bind_ok, Std.uncurry] at h ⊢
    obtain ⟨c, hc, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hc]
    cases c with
    | Err e =>
      simp at h
      subst cf
      exact ⟨.done (.Err e, s, w), by simp, rfl, hrelated⟩
    | Ok u =>
    simp only [bind_ok] at h ⊢
    by_cases he : i = count
    · simp only [he, bne_self_eq_false, Bool.false_eq_true, if_false] at h ⊢
      exact tableRest.refines visitor replacement related hrefines s env count count depth ts arity _
        v w hrelated cf h
    · simp only [bne_iff_ne, if_pos he] at h ⊢
      obtain ⟨⟨reply, v'⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w', hw, hr'⟩ := hrefines v w (.op s.core (.br_table_label depth)) reply v' hrelated hv
      change replacement.on_br_table_label w s.core depth = .ok (reply, w') at hw
      rw [hw]
      cases reply with
      | Err e =>
        simp [code.visit] at h ⊢
        subst cf
        exact ⟨rfl, hr'⟩
      | Ok u =>
        simp [code.visit] at h ⊢
        exact tableRest.refines visitor replacement related hrefines s env count i depth ts arity _
          v' w' hr' cf h

end Itasca.Wasm2.Visitor

namespace Itasca

open VisitorTrace Wasm2.Visitor

/-- Exact refinement of every table-loop outcome, including a partial vector
ending at a rejected label or failed target check. -/
theorem code.branch_table_with_loop.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (v : V) (w : W) (hrelated : related v w)
    (count : U32) (arity : Option Usize) (first : signature.ResultType) (i : U32)
    (hi : i.val ≤ count.val)
    (res : core.result.Result Unit error.OpError) (final : code.BodyState) (v' : V)
    (h : code.branch_table_with_loop visitor st.core data env profile v count arity first i =
      .ok (res, final, v')) :
    ∃ w', code.branch_table_with_loop replacement st.core data env profile w count arity first i =
      .ok (res, final, w') ∧ related v' w' := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st v w arity first i with
  | h n ih =>
    unfold code.branch_table_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [tableBody_eq visitor data env profile count st v arity first i] at h
    simp only [tableBody_eq replacement data env profile count st w arity first i]
    obtain ⟨cf, hs, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    obtain ⟨cf', hw, ho, hr⟩ := tableBody.refines visitor replacement related hrefines
      data env profile count st v w hrelated arity first i cf hs
    rw [hw]
    cases cf with
    | done result =>
      obtain ⟨r, s, v1⟩ := result
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      cases cf' with
      | cont p => simp [tableObserve] at ho
      | done p =>
        obtain ⟨r, s, w'⟩ := p
        simp only [tableObserve, ControlFlow.done.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        exact ⟨w', by simp, hr⟩
    | cont next =>
      obtain ⟨ois, v1, arity1, first1, j⟩ := next
      have hp := tableBody.cont_progress visitor data env profile count st v arity first i
        ois v1 arity1 first1 j hi hs
      cases cf' with
      | done p => simp [tableObserve] at ho
      | cont p =>
        obtain ⟨ois', w1, arity1', first1', j'⟩ := p
        simp only [tableObserve, ControlFlow.cont.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ho
        have hrec : code.branch_table_with_loop visitor ois' data env profile v1 count arity1'
            first1' j' = .ok (res, final, v') := ht
        obtain ⟨w', hw', hr'⟩ := ih (count.val - j'.val) (by omega)
          ⟨ois'⟩ v1 w1 hr arity1' first1' j' hp.2 hrec rfl
        exact ⟨w', by simpa only [bind_ok, code.branch_table_with_loop] using hw', hr'⟩

theorem code.branch_table_with.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.BodyState) (v' : V)
    (h : code.branch_table_with visitor st data env profile v = .ok (res, final, v')) :
    ∃ w', code.branch_table_with replacement st data env profile w =
      .ok (res, final, w') ∧ related v' w' := by
  unfold code.branch_table_with at h ⊢
  obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, hrelated⟩
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
    obtain ⟨⟨r, ois⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hrelated⟩
    | Ok u =>
      simp only [bind_ok, Std.uncurry] at h ⊢
      exact code.branch_table_with_loop.refines visitor replacement related hrefines
        ⟨ois⟩ data env profile v w hrelated count none .Empty 0#u32 (by simp) res final v' h

end Itasca

namespace Itasca

open VisitorTrace Wasm2.Visitor

set_option maxHeartbeats 2000000 in
/-- Profile dispatch, including control instructions, preserves every ordinary result under exact
callback refinement, including computed signatures and partial tables. -/
theorem code.step_profile.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) (opcode : U8)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.BodyState) (v' : V)
    (h : code.step_profile visitor st data env ctx index profile opcode v =
      .ok (res, final, v')) :
    ∃ w', code.step_profile replacement st data env ctx index profile opcode w =
      .ok (res, final, w') ∧ related v' w' := by
  unfold code.step_profile at h ⊢
  obtain ⟨rc, hrc, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hrc]
  cases rc with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, hrelated⟩
  | Ok u =>
  cases u
  have hok : core.result.Result.Insts.CoreOpsTry.branch
      (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
  simp only [bind_ok] at h ⊢
  rw [hok] at h ⊢
  simp only [bind_ok] at h ⊢
  split at h
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_10 | h_11 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, s⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hrelated⟩
    | Ok a =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨⟨reply, v1⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      first
      | (change invoke visitor v (.op s.core (.block a)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.block a)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.loop a)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.loop a)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.if_ a)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.if_ a)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.else_ a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.else_ a.2)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.end_ a.1 a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.end_ a.1 a.2)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.br a.1 a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.br a.1 a.2)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.br_if a.1 a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.br_if a.1 a.2)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.call a)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.call a)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.call_indirect a.1 a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.call_indirect a.1 a.2)) reply v1 hrelated hv)
      all_goals
        simp only [invoke] at hw
        rw [hw]
        cases reply <;> simp [code.visit,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
        all_goals obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, hr1⟩
  case h_8 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, s, v1⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    obtain ⟨w1, hw, hr1⟩ := code.branch_table_with.refines visitor replacement related hrefines
      st data env profile v w hrelated r s v1 hs
    rw [hw]
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
    all_goals obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, hr1⟩
  case h_9 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, ois⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hrelated⟩
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨ois', ho, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rw [ho]
      simp only [bind_ok]
      obtain ⟨⟨reply, v1⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op ois' .return_) reply v1 hrelated hv
      change replacement.on_return w ois' = .ok (reply, w1) at hw
      rw [hw]
      cases reply <;> simp [code.visit,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      all_goals obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, hr1⟩
  case h_12 =>
    try simp_all only
    split at h
    · rename_i hcap
      simp only [hcap, if_true]
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨w, rfl, hrelated⟩
    · rename_i hcap
      simp only [hcap, if_false]
      obtain ⟨⟨r, ois, v1⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w1, hw, hr1⟩ := code.step_wasm2.refines visitor replacement related hrefines
        st.core data env ctx opcode v w hrelated r ois v1 hs
      rw [hw]
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      all_goals obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, hr1⟩

end Itasca
