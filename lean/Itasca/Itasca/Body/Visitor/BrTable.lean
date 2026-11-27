import Itasca.Support.Translation
import Itasca.Visitor.Total
import Itasca.Body.Step.Total
import Itasca.Visitor.RunTrace
import Itasca.Body.EmptyVisitorLoop
import Itasca.Body.Control.EnterSound

/-!
Proofs for Body / Visitor.

This module collects BrTable, Step, Total.
Each section documents its contracts and consumers.
-/

/-! ## BrTable -/

section

/-!
# Visitor transfer for `br_table`

Factors the extracted `code.branch_table_with_loop` body into `tableBody`, `tableRest` and
`tableCheck`, and proves that a successful table iteration transfers to any replacement visitor
with accepting callbacks while preserving the observed validator state (`tableBody.transfer`).
`code.branch_table_with_loop.accepted_transfer` and `code.branch_table_with.accepted_transfer`
lift this to the whole loop and to the selector-decoding wrapper.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Body.Visitor

/-- The suffix check of one `br_table` target, factored from the extracted loop. It compares the
target arity with the first target's arity and checks the operand suffix. -/
def tableCheck (st : code.BodyState) (env : metadata.Env) (ts : signature.ResultType)
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
    (env : metadata.Env) (count i depth : U32) (ts : signature.ResultType)
    (arity : Option Usize) (v : V) :
    Result (ControlFlow (code.OpIterState × V × Option Usize × U32)
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
      .ok (.cont (st.core, v, nextArity, j))

/-- One iteration of the `br_table` target loop: reads a label, calls the label callback for
every target but the default, and continues with `tableRest`. -/
def tableBody {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (count : U32) (st : code.BodyState)
    (v : V) (arity : Option Usize) (i : U32) :
    Result (ControlFlow (code.OpIterState × V × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V)) := do
  let (r, s) ← code.read_label_info st data
  match r with
  | .Err e => .ok (.done (.Err e, s, v))
  | .Ok (depth, ts) =>
    if i != count then
      let (r, v') ← visitor.on_br_table_label v s.core depth
      let r ← code.visit r
      match r with
      | .Err e => .ok (.done (.Err e, s, v'))
      | .Ok () => tableRest visitor s env count i depth ts arity v'
    else tableRest visitor s env count i depth ts arity v

set_option maxHeartbeats 1000000 in
/-- The transfer adapter is an exact factorization of the extracted loop body. -/
theorem table_body_eq {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (count : U32) (st : code.BodyState)
    (v : V) (arity : Option Usize) (i : U32) :
    code.branch_table_with_loop.body visitor data env count st.core v arity i =
      tableBody visitor data env count st v arity i := by
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
    ControlFlow (code.OpIterState × V × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V) →
    ControlFlow (code.OpIterState × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState)
  | .cont (core, _, arity, i) => .cont (core, arity, i)
  | .done (r, st, _) => .done (r, st)

/-- A table iteration result that continues or returns `Ok ()`. -/
def tableGood {V : Type} (cf :
    ControlFlow (code.OpIterState × V × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V)) : Prop :=
  match cf with
  | .cont _ => True
  | .done (r, _, _) => r = .Ok ()

/-- Accepting replacements preserve each successful table continuation. -/
theorem tableRest.transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : Visitor.Accepts replacement)
    (st : code.BodyState) (env : metadata.Env) (count i depth : U32)
    (ts : signature.ResultType) (arity : Option Usize) (v : V) (w : W) (cf)
    (h : tableRest visitor st env count i depth ts arity v = .ok cf)
    (hg : tableGood cf) :
    ∃ cf', tableRest replacement st env count i depth ts arity w = .ok cf' ∧
      tableObserve cf' = tableObserve cf := by
  unfold tableRest at h ⊢
  obtain ⟨r, hr, h⟩ := Computation.bind_ok_inv _ _ _ h
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
      obtain ⟨ois, ho, h⟩ := Computation.bind_ok_inv _ _ _ h
      rw [ho]
      simp only [bind_ok]
      obtain ⟨⟨reply, v'⟩, hv, h⟩ := Computation.bind_ok_inv _ _ _ h
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
      obtain ⟨j, hj, h⟩ := Computation.bind_ok_inv _ _ _ h
      simp only [ok.injEq] at h
      subst cf
      exact ⟨.cont (st.core, w, nextArity, j), by simp [hj], rfl⟩

/-- One actual table iteration transfers without requiring source hooks to be
returning on any unrelated execution. -/
theorem tableBody.transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : Visitor.Accepts replacement)
    (data : Slice U8) (env : metadata.Env) (count : U32)
    (st : code.BodyState) (v : V) (w : W) (arity : Option Usize) (i : U32) (cf)
    (h : tableBody visitor data env count st v arity i = .ok cf)
    (hg : tableGood cf) :
    ∃ cf', tableBody replacement data env count st w arity i = .ok cf' ∧
      tableObserve cf' = tableObserve cf := by
  unfold tableBody at h ⊢
  obtain ⟨⟨r, s⟩, hr, h⟩ := Computation.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp at h
    subst cf
    simp [tableGood] at hg
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [bind_ok, Std.uncurry] at h ⊢
    by_cases he : i = count
    · simp only [he, bne_self_eq_false, Bool.false_eq_true, if_false] at h ⊢
      exact tableRest.transfer visitor replacement ha s env count count depth ts arity v w cf h hg
    · simp only [bne_iff_ne, if_pos he] at h ⊢
      obtain ⟨⟨reply, v'⟩, hv, h⟩ := Computation.bind_ok_inv _ _ _ h
      cases reply with
      | Err e =>
        simp [code.visit] at h
        subst cf
        simp [tableGood] at hg
      | Ok u =>
        simp [code.visit] at h
        obtain ⟨w', hw⟩ := ha.on_br_table_label w s.core depth
        simp [hw, code.visit]
        exact tableRest.transfer visitor replacement ha s env count i depth ts arity v' w' cf h hg

theorem tableRest.cont_progress {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (env : metadata.Env) (count i depth : U32)
    (ts : signature.ResultType) (arity : Option Usize) (v : V)
    (ois : code.OpIterState)
    (v' : V) (arity' : Option Usize) (j : U32)
    (hi : i.val ≤ count.val)
    (h : tableRest visitor st env count i depth ts arity v =
      .ok (.cont (ois, v', arity', j))) :
    i.val < j.val ∧ j.val ≤ count.val := by
  unfold tableRest at h
  obtain ⟨r, hr, h⟩ := Computation.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp at h
  | Ok nextArity =>
    simp only at h
    by_cases he : i = count
    · simp only [he, if_true] at h
      obtain ⟨ois, ho, h⟩ := Computation.bind_ok_inv _ _ _ h
      obtain ⟨⟨r, w⟩, hv, h⟩ := Computation.bind_ok_inv _ _ _ h
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
    (data : Slice U8) (env : metadata.Env) (count : U32)
    (st : code.BodyState) (v : V) (arity : Option Usize) (i : U32)
    (ois : code.OpIterState)
    (v' : V) (arity' : Option Usize) (j : U32)
    (hi : i.val ≤ count.val)
    (h : tableBody visitor data env count st v arity i =
      .ok (.cont (ois, v', arity', j))) :
    i.val < j.val ∧ j.val ≤ count.val := by
  unfold tableBody at h
  obtain ⟨⟨r, s⟩, hr, h⟩ := Computation.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp at h
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [Std.uncurry] at h
    by_cases he : i = count
    · simp only [he, bne_self_eq_false, Bool.false_eq_true, if_false] at h
      simpa only [he] using tableRest.cont_progress visitor s env count count depth ts arity v
        ois v' arity' j (by simp) h
    · simp only [bne_iff_ne, if_pos he] at h
      obtain ⟨⟨r, w⟩, hv, h⟩ := Computation.bind_ok_inv _ _ _ h
      cases r with
      | Err e => simp [code.visit] at h
      | Ok u =>
        simp only [code.visit, bind_ok, Std.uncurry] at h
        exact tableRest.cont_progress visitor s env count i depth ts arity w
          ois v' arity' j hi h

end Itasca.Body.Visitor

namespace Itasca

open Body.Visitor

/-- Successful branch-table execution transfers to every accepting replacement,
with exactly the same validation state. -/
theorem code.branch_table_with_loop.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : Visitor.Accepts replacement) (st : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (v : V) (w : W)
    (count : U32) (arity : Option Usize) (i : U32)
    (hi : i.val ≤ count.val) (final : code.BodyState) (v' : V)
    (h : code.branch_table_with_loop visitor st.core data env v count arity i =
      .ok (.Ok (), final, v')) :
    ∃ w', code.branch_table_with_loop replacement st.core data env w count arity i =
      .ok (.Ok (), final, w') := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st v w arity i with
  | h n ih =>
    unfold code.branch_table_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [table_body_eq visitor data env count st v arity i] at h
    simp only [table_body_eq replacement data env count st w arity i]
    obtain ⟨cf, hs, ht⟩ := Computation.bind_ok_inv _ _ _ h
    cases cf with
    | done result =>
      obtain ⟨r, s, v1⟩ := result
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      obtain ⟨cf, hw, ho⟩ := tableBody.transfer visitor replacement ha data env count st
        v w arity i _ hs rfl
      rw [hw]
      cases cf with
      | cont p => simp [tableObserve] at ho
      | done p =>
        obtain ⟨r, s, w'⟩ := p
        simp only [tableObserve, ControlFlow.done.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        exact ⟨w', by simp⟩
    | cont next =>
      obtain ⟨ois, v1, arity1, j⟩ := next
      have hp := tableBody.cont_progress visitor data env count st v arity i
        ois v1 arity1 j hi hs
      obtain ⟨cf, hw, ho⟩ := tableBody.transfer visitor replacement ha data env count st
        v w arity i _ hs trivial
      rw [hw]
      cases cf with
      | done p => simp [tableObserve] at ho
      | cont p =>
        obtain ⟨ois', w1, arity1', j'⟩ := p
        simp only [tableObserve, ControlFlow.cont.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl, rfl⟩ := ho
        have hrec : code.branch_table_with_loop visitor ois' data env v1 count arity1'
            j' = .ok (.Ok (), final, v') := ht
        obtain ⟨w', hw'⟩ := ih (count.val - j'.val) (by omega)
          ⟨ois'⟩ v1 w1 arity1' j' hp.2 hrec rfl
        exact ⟨w', by simpa only [bind_ok, code.branch_table_with_loop] using hw'⟩

/-- The wrapper's shared selector decoding preserves visitor transfer. -/
theorem code.branch_table_with.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : Visitor.Accepts replacement) (st : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (v : V) (w : W)
    (final : code.BodyState) (v' : V)
    (h : code.branch_table_with visitor st data env v = .ok (.Ok (), final, v')) :
    ∃ w', code.branch_table_with replacement st data env w = .ok (.Ok (), final, w') := by
  unfold code.branch_table_with at h ⊢
  obtain ⟨r, hr, h⟩ := Computation.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
    obtain ⟨⟨r, ois⟩, hr, h⟩ := Computation.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      simp only [bind_ok, Std.uncurry] at h ⊢
      exact code.branch_table_with_loop.accepted_transfer visitor replacement ha
        ⟨ois⟩ data env v w count none 0#u32 (by simp) final v' h

end Itasca

end

/-! ## Step -/

section

/-!
# Visitor transfer for one Wasm 2.0 step

`step_transfer` shows that a successful `code.step_body` under one visitor succeeds under any
replacement visitor with accepting callbacks, ending in the same validator state.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Body.Visitor

set_option maxHeartbeats 2000000 in
/-- Accepting hooks preserve successful Wasm 2.0 steps and the exact
validator state. Scalar steps depend on locals, not the context result vector. -/
theorem step_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : Visitor.Accepts replacement)
    (data : Slice U8) (env : metadata.Env) (ctx ctx' : code.Context)
    (hlocals : ctx.locals = ctx'.locals) (index : U32) (opcode : U8)
    (st final : code.BodyState) (v : V) (w : W) (v' : V)
    (h : code.step_body visitor st data env ctx index opcode v =
      .ok (.Ok (), final, v')) :
    ∃ w', code.step_body replacement st data env ctx' index opcode w =
      .ok (.Ok (), final, w') := by
  unfold code.step_body at h ⊢
  split at h
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_10 | h_11 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, s⟩, hr, h⟩ := Computation.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok a =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨⟨r, v'⟩, hv, h⟩ := Computation.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [code.visit,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok u =>
        simp [code.visit] at h
        obtain ⟨rfl, rfl⟩ := h
        solve
        | (obtain ⟨w', hw⟩ := ha.on_block w s.core a
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_loop w s.core a
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_if w s.core a
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_else w s.core a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_end w s.core a.1 a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_br w s.core a.1 a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_br_if w s.core a.1 a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_call w s.core a
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_call_indirect w s.core a.1 a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
  case h_8 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, s, v'⟩, hs, h⟩ := Computation.bind_ok_inv _ _ _ h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      cases u
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨w', hw⟩ := code.branch_table_with.accepted_transfer visitor replacement ha
        st data env v w s v' hs
      exact ⟨w', by simp [hw, core.result.Result.Insts.CoreOpsTry.branch]⟩
  case h_9 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, ois⟩, hr, h⟩ := Computation.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨ois', ho, h⟩ := Computation.bind_ok_inv _ _ _ h
      rw [ho]
      simp only [bind_ok]
      obtain ⟨⟨r, v'⟩, hv, h⟩ := Computation.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [code.visit,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok u =>
        simp [code.visit] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨w', hw⟩ := ha.on_return w ois'
        exact ⟨w', by simp [hw, code.visit]⟩
  case h_12 =>
    rename_i _ h2 h3 h4 h5 h11 h12 h13 h14 h15 h16 h17
    have hscalar : opcode.val ∉ controlOpcodes := by
      have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val :=
        fun he => h (UScalar.eq_of_val_eq he)
      simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨neq h2, neq h3, neq h4, neq h5, neq h11, neq h12,
        neq h13, neq h14, neq h15, neq h16, neq h17⟩
    try simp_all only
    split at h
    · simp at h
    · rename_i hcap
      simp only [hcap, if_false]
      obtain ⟨⟨r, ois, v'⟩, hs, h⟩ := Computation.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok u =>
        cases u
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨w', hw⟩ := instruction_transfer visitor replacement ha
          st.core ois data env ctx ctx' opcode v v' w hscalar hlocals hs
        exact ⟨w', by simp [hw, core.result.Result.Insts.CoreOpsTry.branch]⟩

end Itasca.Body.Visitor

end

/-! ## Total -/

section

/-!
# Totality of visiting body validation

Shows that `code.validate_body_with` terminates for every input when the visitor's
callbacks return (`Visitor.Total`), without byte validity or environment hypotheses
(`code.validate_body_with.total`). The supporting lemmas cover the body loop
(`code.body_loop_loop.total`), its initial state, branch tables and branch information; each
iteration preserves `Body.Control.Shape` and advances the cursor.
-/

open Aeneas Aeneas.Std

namespace Itasca

@[step] theorem code.branch_info.total (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (conditional : Bool) (hs : Body.Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch_info st data env conditional ⦃ r =>
      Body.Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ :=
  by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.branch.total st data env conditional hs ha)
  unfold code.branch at hr
  obtain ⟨⟨result, out⟩, hs, hnext⟩ := Computation.bind_ok_inv _ _ _ hr
  rw [hs, WP.spec_ok]
  cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
  all_goals subst r; exact hp

@[step] theorem code.end_frame_info.total (st : code.BodyState) (env : metadata.Env)
    (isElse : Bool) (hs : Body.Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.end_frame_info st env isElse ⦃ r =>
      Body.Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks.val.length ≤ st.blocks.val.length ∧ r.2.core.pos = st.core.pos ⦄ :=
  by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.end_frame.total st env isElse hs ha)
  unfold code.end_frame at hr
  obtain ⟨⟨result, out⟩, hs, hnext⟩ := Computation.bind_ok_inv _ _ _ hr
  rw [hs, WP.spec_ok]
  cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
  all_goals subst r; exact hp

@[step] theorem code.read_label_info.total (st : code.BodyState) (data : Slice U8)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_label_info st data ⦃ r =>
      r.2.core.vals = st.core.vals ∧ r.2.core.ctrls = st.core.ctrls ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.read_multi_value_label.spec st data ha)
  unfold code.read_multi_value_label at hr
  obtain ⟨⟨result, out⟩, hs, hnext⟩ := Computation.bind_ok_inv _ _ _ hr
  rw [hs, WP.spec_ok]
  cases result with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
    subst r
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hnext
    subst r
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

attribute [local step] code.pop_with_type.total code.check_suffix.spec

@[local step] private theorem label_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (depth : U32) :
    visitor.on_br_table_label v st depth ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_br_table_label v st depth
  simp [h]

@[local step] private theorem table_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (depth : U32)
    (ts : signature.ResultType) :
    visitor.on_br_table v st depth ts ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_br_table v st depth ts
  simp [h]

@[local step] private theorem visit_total (r : core.result.Result Unit error.VisitError) :
    code.visit r ⦃ _ => True ⦄ := by
  cases r <;> simp [code.visit]

/-- Returning hooks preserve the structural branch-table invariant, including
rejections and the default target at the maximal encoded count. -/
theorem code.branch_table_with_loop.total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (v : V) (count : U32) (arity : Option Usize)
    (i : U32)
    (hs : Body.Control.Shape st.core) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hi : i.val ≤ count.val) :
    code.branch_table_with_loop visitor st.core data env v count arity i ⦃ r =>
      Body.Control.Shape r.2.1.core ∧ r.2.1.blocks.val.length = r.2.1.core.ctrls.val.length ∧
      r.2.1.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.1.core.pos.val ⦄ := by
  unfold code.branch_table_with_loop
  apply loop.spec_decr_nat (fun p => count.val - p.2.2.2.val)
    (fun p => Body.Control.Shape p.1 ∧ (code.BodyState.mk p.1).blocks.val.length = p.1.ctrls.val.length ∧
      (code.BodyState.mk p.1).blocks = st.blocks ∧ p.2.2.2.val ≤ count.val ∧
      st.core.pos.val ≤ p.1.pos.val)
  · rintro ⟨stateCore, v, arity, j⟩ ⟨hs', ha', hb', hj, hpos⟩
    dsimp only at hs' ha' hb' hj hpos
    dsimp only
    unfold code.branch_table_with_loop.body
    obtain ⟨⟨r, s⟩, hr, hvals, hc, hb, hp⟩ := WP.spec_imp_exists
      (code.read_label_info.total ⟨stateCore⟩ data ha')
    rw [hr]
    simp only [bind_ok]
    dsimp only at hvals hc hb hp
    have hss : Body.Control.Shape s.core :=
      ⟨by simpa [hc] using hs'.ordered, by simpa [hc, hvals] using hs'.bounded⟩
    have has : s.blocks.val.length = s.core.ctrls.val.length := by simp_all
    have hbs : s.blocks = st.blocks := by simp_all
    have hprogress : st.core.pos.val ≤ s.core.pos.val := by omega
    cases r with
    | Err e => simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨depth, ts⟩ := pair
      have hbranch : core.result.Result.Insts.CoreOpsTry.branch
          (.Ok (depth, ts) : core.result.Result (U32 × signature.ResultType) error.OpError) =
          .ok (.Continue (depth, ts)) := rfl
      simp only [Std.uncurry, hbranch, bind_ok]
      cases arity <;> step* by simp_all
      all_goals scalar_tac
  · exact ⟨hs, ha, rfl, hi, le_refl _⟩

@[step]
theorem code.branch_table_with.total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (v : V) (hs : Body.Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch_table_with visitor st data env v ⦃ r =>
      Body.Control.Shape r.2.1.core ∧ r.2.1.blocks.val.length = r.2.1.core.ctrls.val.length ∧
      r.2.1.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.1.core.pos.val ⦄ := by
  unfold code.branch_table_with
  step with reader.read_u32_leb.spec data st.core.pos as ⟨res, hdecoded⟩
  step
  split
  · rename_i _ pair
    obtain ⟨count, next⟩ := pair
    have hpnext : st.core.pos.val ≤ next.val := by
      cases res <;> simp_all [Binary.Leb128.Post]
      cases cf_post
      exact (Binary.Leb128.Decoded.span _ _ _ _ hdecoded).1.le
    have hspos : Body.Control.Shape { st.core with pos := next } := ⟨hs.ordered, hs.bounded⟩
    step with code.pop_with_type.total _ .I32 hspos as ⟨r, s, hs', hc, hp, hvals, he⟩
    step
    split
    · apply WP.spec_mono (code.branch_table_with_loop.total visitor hv
        ⟨s⟩ data env v count none 0#u32 hs' (by simp_all) (by simp))
      intro result hout
      exact ⟨hout.1, hout.2.1, by simpa [hc] using hout.2.2.1, hpnext.trans (by simpa [hp] using hout.2.2.2)⟩
    · step*
      simp_all
  · step*

@[local step] private theorem block_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (bt : signature.BlockType) :
    visitor.on_block v st bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_block v st bt
  simp [h]

@[local step] private theorem loop_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (bt : signature.BlockType) :
    visitor.on_loop v st bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_loop v st bt
  simp [h]

@[local step] private theorem if_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (bt : signature.BlockType) :
    visitor.on_if v st bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_if v st bt
  simp [h]

@[local step] private theorem else_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (bt : signature.BlockType) :
    visitor.on_else v st bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_else v st bt
  simp [h]

@[local step] private theorem end_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType) :
    visitor.on_end v st kind bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_end v st kind bt
  simp [h]

@[local step] private theorem br_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (depth : U32) (ts : signature.ResultType) :
    visitor.on_br v st depth ts ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_br v st depth ts
  simp [h]

@[local step] private theorem br_if_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (depth : U32) (ts : signature.ResultType) :
    visitor.on_br_if v st depth ts ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_br_if v st depth ts
  simp [h]

@[local step] private theorem return_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) :
    visitor.on_return v st ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_return v st
  simp [h]

@[local step] private theorem call_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (index : U32) :
    visitor.on_call v st index ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_call v st index
  simp [h]

@[local step] private theorem call_indirect_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (v : V) (st : code.OpIterState) (index table : U32) :
    visitor.on_call_indirect v st index table ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_call_indirect v st index table
  simp [h]

attribute [local step] code.enter_info.total

set_option maxHeartbeats 2000000 in
/-- Every returned body iteration preserves the structural invariant and every
continuing iteration advances the byte cursor. Returning hooks may reject. -/
theorem code.body_loop_loop.body.total {V : Type}
    (visitor : code.OpVisitor V) (hv : Visitor.Total visitor)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (type_index : U32)
     (s : code.BodyState) (v : V)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Body.Control.Shape s.core)
    (ha : s.blocks.val.length = s.core.ctrls.val.length)
    (hb : s.blocks.val.length ≤ s.core.pos.val + 1) :
    code.body_loop_loop.body visitor data env ctx type_index v s ⦃ r =>
      match r with
      | .done _ => True
      | .cont p => (Body.Control.Shape p.2.core ∧
          p.2.blocks.val.length = p.2.core.ctrls.val.length ∧
          p.2.blocks.val.length ≤ p.2.core.pos.val + 1) ∧
          Usize.max - p.2.core.pos.val < Usize.max - s.core.pos.val ⦄ := by
  unfold code.body_loop_loop.body code.step_body
  simp only [alloc.vec.Vec.is_empty, bind_ok]
  split
  · split <;> simp
  · by_cases hp : s.core.pos.val < data.length
    · obtain ⟨res, hr, next, hres, hn⟩ := WP.spec_imp_exists
        (reader.read_byte.spec data s.core.pos hp)
      rw [hres] at hr
      rw [hr]
      simp only [bind_ok]
      have hbranch : core.result.Result.Insts.CoreOpsTry.branch
          (.Ok (data.val[s.core.pos.val], next) : core.result.Result (U8 × Usize) error.OpError) =
          .ok (.Continue (data.val[s.core.pos.val], next)) := rfl
      rw [hbranch]
      simp only [bind_ok, Std.uncurry]
      have hspos : Body.Control.Shape { s.core with pos := next } := ⟨hs.ordered, hs.bounded⟩
      have hcap : s.blocks.val.length < Usize.max := by
        have := limits.MAX_FUNCTION_BYTES.room
        omega
      have hpos : s.core.pos.val < Usize.max := by
        have := limits.MAX_FUNCTION_BYTES.room
        omega
      split
      all_goals try simp only [Std.bind_assoc, Std.uncurry]
      case h_12 =>
        rename_i _ h2 h3 h4 h5 h11 h12 h13 h14 h15 h16 h17
        have hscalar : (data.val[s.core.pos.val]).val ∉ Body.controlOpcodes := by
          have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val :=
            fun he => h (UScalar.eq_of_val_eq he)
          simp only [Body.controlOpcodes, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨neq h2, neq h3, neq h4, neq h5, neq h11, neq h12,
            neq h13, neq h14, neq h15, neq h16, neq h17⟩
        split
        · simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · have hsize : s.core.vals.val.length < Usize.max := by scalar_tac
          step with Body.instruction_total visitor
            { s.core with pos := next } data env ctx
            data.val[s.core.pos.val] v hspos hsize hscalar hv
            as ⟨r, hsc, hcount, hp'⟩
          rcases r with ⟨r, sc, v'⟩
          cases r <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          scalar_tac
      all_goals step*
      all_goals try (cases x)
      all_goals try simp only [Std.bind_assoc, Std.uncurry]
      all_goals step*
      all_goals try (cases x)
      all_goals try simp only [Std.bind_assoc]
      all_goals step*
      all_goals simp_all
      all_goals try constructor
      all_goals scalar_tac
    · rw [reader.read_byte.eof data s.core.pos (by omega)]
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

set_option maxHeartbeats 2000000 in
/-- The actual visiting body loop terminates for structurally bounded states.
Every continuing iteration consumes an opcode; rejecting hooks terminate early. -/
theorem code.body_loop_loop.total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (type_index : U32) (st : code.BodyState)
    (v : V) (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Body.Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hb : st.blocks.val.length ≤ st.core.pos.val + 1) :
    code.body_loop_loop visitor data env ctx type_index v st ⦃ _ => True ⦄ := by
  unfold code.body_loop_loop
  apply loop.spec_decr_nat (fun p => Usize.max - p.2.core.pos.val)
    (fun p => Body.Control.Shape p.2.core ∧ p.2.blocks.val.length = p.2.core.ctrls.val.length ∧
      p.2.blocks.val.length ≤ p.2.core.pos.val + 1)
  · rintro ⟨v, s⟩ ⟨hs, ha, hb⟩
    dsimp only
    apply WP.spec_mono (code.body_loop_loop.body.total visitor hv data env ctx type_index
      s v hdata hs ha hb)
    intro r hr
    cases r <;> exact hr
  · exact ⟨hs, ha, hb⟩

attribute [local step] code.body_loop_loop.total

/-- Initialization is total and supplies the shared loop invariant. -/
@[step] theorem code.initial_state.total (env : metadata.Env) (index : U32) :
    code.initial_state env index ⦃ r =>
      match r with
      | .Err _ => True
      | .Ok st => Body.Control.Shape st.core ∧
          st.blocks.val.length = st.core.ctrls.val.length ∧
          st.blocks.val.length ≤ st.core.pos.val + 1 ⦄ := by
  have hi : Body.Control.Shape
      { vals := alloc.vec.Vec.new _, ctrls := alloc.vec.Vec.new _, pos := 0#usize } :=
    ⟨by simp, by simp⟩
  unfold code.initial_state
  step* <;> simp_all; scalar_tac

/-- Returning opcode hooks suffice for totality on arbitrary input in the unified validator; no byte
validity, signature, or environment hypothesis is required. -/
theorem code.validate_body_with.total {V : Type} (visitor : code.OpVisitor V)
    (hv : Visitor.Total visitor) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (type_index : U32) (v : V) :
    ∃ r, code.validate_body_with visitor data env ctx type_index v = .ok r := by
  have ht : code.validate_body_with visitor data env ctx type_index v ⦃ _ => True ⦄ := by
    unfold code.validate_body_with
    simp only [Slice.len]
    split
    · simp
    · have hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val := by scalar_tac
      step with code.initial_state.total env type_index as ⟨r, hr⟩
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok st =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.body_loop]
        exact code.body_loop_loop.total visitor hv data env ctx type_index st v
          hdata hr.1 hr.2.1 hr.2.2
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists ht
  exact ⟨r, hr⟩

end Itasca

end
