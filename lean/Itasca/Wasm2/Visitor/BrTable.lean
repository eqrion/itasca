import Itasca.Support.BodyState
import Itasca.Visitor.Accepts
import Itasca.Support.Result

/-!
# Visitor transfer for `br_table`

Factors the extracted `code.branch_table_with_loop` body into `tableBody`, `tableRest` and
`tableCheck`, and proves that a successful table iteration transfers to any replacement visitor
with accepting callbacks while preserving the observed validator state (`tableBody.transfer`).
`code.branch_table_with_loop.accepted_transfer` and `code.branch_table_with.accepted_transfer`
lift this to the whole loop and to the selector-decoding wrapper.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Wasm2.Visitor

/-- The suffix check of one `br_table` target, factored from the extracted loop. It compares the
target arity with the first target's arity and checks the operand suffix. -/
def tableCheck (st : code.BodyState) (env : module.Env) (ts : signature.ResultType)
    (arity : Option Usize) : Result (core.result.Result (Option Usize) error.OpError) := do
  let r ← signature.ResultType.len ts env
  match r with
  | .Err e => .ok (.Err e)
  | .Ok n =>
    match arity with
    | none =>
      let r ← code.check_suffix st.core env ts
      match r with
      | .Err e => .ok (.Err e)
      | .Ok () => .ok (.Ok (some n))
    | some expected =>
      if expected != n then .ok (.Err .TypeMismatch) else
        let r ← code.check_suffix st.core env ts
        match r with
        | .Err e => .ok (.Err e)
        | .Ok () => .ok (.Ok arity)

/-- The part of a table iteration after its label callback: checks the target, and at the default
target (`i = count`) marks the code unreachable and calls the `br_table` callback. -/
def tableRest {V : Type} (visitor : code.OpVisitor V) (st : code.BodyState)
    (env : module.Env) (count i depth : U32) (ts : signature.ResultType)
    (arity : Option Usize) (first : signature.ResultType) (v : V) :
    Result (ControlFlow (code.OpIterState × V × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V)) := do
  let r ← tableCheck st env ts arity
  match r with
  | .Err e => .ok (.done (.Err e, st, v))
  | .Ok nextArity =>
    if i = count then
      let ois ← code.mark_unreachable st.core
      let (r, v') ← visitor.on_br_table v ois depth ts
      let r ← code.visit r
      .ok (.done (r, { st with core := ois }, v'))
    else
      let j ← i + 1#u32
      .ok (.cont (st.core, v, nextArity, first, j))

/-- One iteration of the `br_table` target loop: reads a label, calls the label callback for
every target but the default, and continues with `tableRest`. -/
def tableBody {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (profile : ValidationProfile) (count : U32) (st : code.BodyState)
    (v : V) (arity : Option Usize) (first : signature.ResultType) (i : U32) :
    Result (ControlFlow (code.OpIterState × V × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V)) := do
  let (r, s) ← code.read_label_info st data
  match r with
  | .Err e => .ok (.done (.Err e, s, v))
  | .Ok (depth, ts) =>
    let first1 := if i = 0#u32 then ts else first
    let r ← code.check_table_target profile env first1 ts
    match r with
    | .Err e => .ok (.done (.Err e, s, v))
    | .Ok () =>
      if i != count then
        let (r, v') ← visitor.on_br_table_label v s.core depth
        let r ← code.visit r
        match r with
        | .Err e => .ok (.done (.Err e, s, v'))
        | .Ok () => tableRest visitor s env count i depth ts arity first1 v'
      else tableRest visitor s env count i depth ts arity first1 v

set_option maxHeartbeats 1000000 in
/-- The transfer adapter is an exact factorization of the extracted loop body. -/
theorem tableBody_eq {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (profile : ValidationProfile) (count : U32) (st : code.BodyState)
    (v : V) (arity : Option Usize) (first : signature.ResultType) (i : U32) :
    code.branch_table_with_loop.body visitor data env profile count st.core v arity first i =
      tableBody visitor data env profile count st v arity first i := by
  simp only [code.branch_table_with_loop.body, tableBody, tableRest, tableCheck,
    Std.bind_assoc]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    by_cases hi : i = count <;> cases arity <;>
      simp [hi, code.visit,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    all_goals
      repeat' first
        | rfl
        | (congr 1; funext x; first
            | (rcases x with ⟨a, b⟩; cases a)
            | cases x
           all_goals simp [Std.bind_assoc])
        | (split <;> simp_all [Std.bind_assoc])
    all_goals
      congr 1
      funext ois
      congr 1
      funext pair
      obtain ⟨r, w⟩ := pair
      cases r <;> simp


/-- State observation of one table iteration, excluding callback bookkeeping. -/
def tableObserve {V : Type} :
    ControlFlow (code.OpIterState × V × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V) →
    ControlFlow (code.OpIterState × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState)
  | .cont (core, _, arity, first, i) => .cont (core, arity, first, i)
  | .done (r, st, _) => .done (r, st)

/-- A table iteration result that continues or returns `Ok ()`. -/
def tableGood {V : Type} (cf :
    ControlFlow (code.OpIterState × V × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V)) : Prop :=
  match cf with
  | .cont _ => True
  | .done (r, _, _) => r = .Ok ()

/-- Accepting replacements preserve each successful table continuation. -/
theorem tableRest.transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (st : code.BodyState) (env : module.Env) (count i depth : U32)
    (ts : signature.ResultType) (arity : Option Usize) (first : signature.ResultType)
    (v : V) (w : W) (cf)
    (h : tableRest visitor st env count i depth ts arity first v = .ok cf)
    (hg : tableGood cf) :
    ∃ cf', tableRest replacement st env count i depth ts arity first w = .ok cf' ∧
      tableObserve cf' = tableObserve cf := by
  unfold tableRest at h ⊢
  obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp only [ok.injEq] at h
    subst cf
    simp [tableGood] at hg
  | Ok nextArity =>
    simp only [bind_ok] at h ⊢
    by_cases he : i = count
    · simp only [he, if_true] at h ⊢
      obtain ⟨ois, ho, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rw [ho]
      simp only [bind_ok]
      obtain ⟨⟨reply, v'⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases reply with
      | Err e =>
        simp [code.visit] at h
        subst cf
        simp [tableGood] at hg
      | Ok u =>
        simp [code.visit] at h
        subst cf
        obtain ⟨w', hw⟩ := ha.on_br_table w ois depth ts
        exact ⟨.done (.Ok (), { st with core := ois }, w'), by simp [hw, code.visit], rfl⟩
    · simp only [he, if_false] at h ⊢
      obtain ⟨j, hj, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      simp only [ok.injEq] at h
      subst cf
      exact ⟨.cont (st.core, w, nextArity, first, j), by simp [hj], rfl⟩

/-- One actual table iteration transfers without requiring source hooks to be
returning on any unrelated execution. -/
theorem tableBody.transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32)
    (st : code.BodyState) (v : V) (w : W) (arity : Option Usize) (first : signature.ResultType)
    (i : U32) (cf)
    (h : tableBody visitor data env profile count st v arity first i = .ok cf)
    (hg : tableGood cf) :
    ∃ cf', tableBody replacement data env profile count st w arity first i = .ok cf' ∧
      tableObserve cf' = tableObserve cf := by
  unfold tableBody at h ⊢
  obtain ⟨⟨r, s⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp at h
    subst cf
    simp [tableGood] at hg
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [bind_ok, Std.uncurry] at h ⊢
    obtain ⟨c, hc, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hc]
    cases c with
    | Err e =>
      simp at h
      subst cf
      simp [tableGood] at hg
    | Ok u =>
    simp only [bind_ok] at h ⊢
    by_cases he : i = count
    · simp only [he, bne_self_eq_false, Bool.false_eq_true, if_false] at h ⊢
      exact tableRest.transfer visitor replacement ha s env count count depth ts arity _ v w cf h hg
    · simp only [bne_iff_ne, if_pos he] at h ⊢
      obtain ⟨⟨reply, v'⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases reply with
      | Err e =>
        simp [code.visit] at h
        subst cf
        simp [tableGood] at hg
      | Ok u =>
        simp [code.visit] at h
        obtain ⟨w', hw⟩ := ha.on_br_table_label w s.core depth
        simp [hw, code.visit]
        exact tableRest.transfer visitor replacement ha s env count i depth ts arity _ v' w' cf h hg


theorem tableRest.cont_progress {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (env : module.Env) (count i depth : U32)
    (ts : signature.ResultType) (arity : Option Usize) (first : signature.ResultType) (v : V)
    (ois : code.OpIterState)
    (v' : V) (arity' : Option Usize) (first' : signature.ResultType) (j : U32)
    (hi : i.val ≤ count.val)
    (h : tableRest visitor st env count i depth ts arity first v =
      .ok (.cont (ois, v', arity', first', j))) :
    i.val < j.val ∧ j.val ≤ count.val := by
  unfold tableRest at h
  obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp at h
  | Ok nextArity =>
    simp only at h
    by_cases he : i = count
    · simp only [he, if_true] at h
      obtain ⟨ois, ho, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨⟨r, w⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r <;> simp [code.visit] at h
    · simp only [he, if_false] at h
      have hlt : i.val < count.val := by
        have hne : i.val ≠ count.val := fun h => he (UScalar.eq_of_val_eq h)
        omega
      obtain ⟨j', hj, hjv⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      simp only [hj, bind_ok, ok.injEq, ControlFlow.cont.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h
      scalar_tac

theorem tableBody.cont_progress {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32)
    (st : code.BodyState) (v : V) (arity : Option Usize) (first : signature.ResultType) (i : U32)
    (ois : code.OpIterState)
    (v' : V) (arity' : Option Usize) (first' : signature.ResultType) (j : U32)
    (hi : i.val ≤ count.val)
    (h : tableBody visitor data env profile count st v arity first i =
      .ok (.cont (ois, v', arity', first', j))) :
    i.val < j.val ∧ j.val ≤ count.val := by
  unfold tableBody at h
  obtain ⟨⟨r, s⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp at h
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [Std.uncurry] at h
    obtain ⟨c, hc, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases c with
    | Err e => simp at h
    | Ok u =>
    simp only [bind_ok] at h
    by_cases he : i = count
    · simp only [he, bne_self_eq_false, Bool.false_eq_true, if_false] at h
      simpa only [he] using tableRest.cont_progress visitor s env count count depth ts arity _ v
        ois v' arity' first' j (by simp) h
    · simp only [bne_iff_ne, if_pos he] at h
      obtain ⟨⟨r, w⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e => simp [code.visit] at h
      | Ok u =>
        simp only [code.visit, bind_ok, Std.uncurry] at h
        exact tableRest.cont_progress visitor s env count i depth ts arity _ w
          ois v' arity' first' j hi h


end Itasca.Wasm2.Visitor

namespace Itasca

open Wasm2.Visitor

/-- Successful branch-table execution transfers to every accepting replacement,
with exactly the same validation state. -/
theorem code.branch_table_with_loop.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : FullVisitor.Accepts replacement) (st : code.BodyState)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (v : V) (w : W)
    (count : U32) (arity : Option Usize) (first : signature.ResultType) (i : U32)
    (hi : i.val ≤ count.val) (final : code.BodyState) (v' : V)
    (h : code.branch_table_with_loop visitor st.core data env profile v count arity first i =
      .ok (.Ok (), final, v')) :
    ∃ w', code.branch_table_with_loop replacement st.core data env profile w count arity first i =
      .ok (.Ok (), final, w') := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st v w arity first i with
  | h n ih =>
    unfold code.branch_table_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [tableBody_eq visitor data env profile count st v arity first i] at h
    simp only [tableBody_eq replacement data env profile count st w arity first i]
    obtain ⟨cf, hs, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases cf with
    | done result =>
      obtain ⟨r, s, v1⟩ := result
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      obtain ⟨cf, hw, ho⟩ := tableBody.transfer visitor replacement ha data env profile count st
        v w arity first i _ hs rfl
      rw [hw]
      cases cf with
      | cont p => simp [tableObserve] at ho
      | done p =>
        obtain ⟨r, s, w'⟩ := p
        simp only [tableObserve, ControlFlow.done.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        exact ⟨w', by simp⟩
    | cont next =>
      obtain ⟨ois, v1, arity1, first1, j⟩ := next
      have hp := tableBody.cont_progress visitor data env profile count st v arity first i
        ois v1 arity1 first1 j hi hs
      obtain ⟨cf, hw, ho⟩ := tableBody.transfer visitor replacement ha data env profile count st
        v w arity first i _ hs trivial
      rw [hw]
      cases cf with
      | done p => simp [tableObserve] at ho
      | cont p =>
        obtain ⟨ois', w1, arity1', first1', j'⟩ := p
        simp only [tableObserve, ControlFlow.cont.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ho
        have hrec : code.branch_table_with_loop visitor ois' data env profile v1 count arity1'
            first1' j' = .ok (.Ok (), final, v') := ht
        obtain ⟨w', hw'⟩ := ih (count.val - j'.val) (by omega)
          ⟨ois'⟩ v1 w1 arity1' first1' j' hp.2 hrec rfl
        exact ⟨w', by simpa only [bind_ok, code.branch_table_with_loop] using hw'⟩

/-- The wrapper's shared selector decoding preserves visitor transfer. -/
theorem code.branch_table_with.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : FullVisitor.Accepts replacement) (st : code.BodyState)
    (data : Slice U8) (env : module.Env) (v : V) (w : W)
    (final : code.BodyState) (v' : V)
    (profile : ValidationProfile)
    (h : code.branch_table_with visitor st data env profile v = .ok (.Ok (), final, v')) :
    ∃ w', code.branch_table_with replacement st data env profile w = .ok (.Ok (), final, w') := by
  unfold code.branch_table_with at h ⊢
  obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
    obtain ⟨⟨r, ois⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      simp only [bind_ok, Std.uncurry] at h ⊢
      exact code.branch_table_with_loop.accepted_transfer visitor replacement ha
        ⟨ois⟩ data env profile v w count none .Empty 0#u32 (by simp) final v' h

end Itasca
