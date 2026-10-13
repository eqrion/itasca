import Itasca.Wasm2.Signature
import Itasca.Handler.Stack

/-!
# Descriptor stack operations

Specs of the extracted operand-stack operations that take a `signature.ResultType` descriptor:
`code.check_func_type`, `code.push_results` and `code.pop_results`. `push_results.spec` and
`pop_results.concrete` and `.polymorphic` describe their effect on the stack for a resolved
descriptor, and the semantic and totality statements are in `Wasm2/ResultStackSemantics`.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.check_func_type` accepts exactly the function types within the parameter and result
limits and reports which limit is exceeded otherwise. -/
@[step]
theorem code.check_func_type.spec (ft : types.FuncType) :
    code.check_func_type ft ⦃ r =>
      match r with
      | .Ok _ => ft.params.val.length ≤ 1000 ∧ ft.results.val.length ≤ 1000
      | .Err .TooManyParams => 1000 < ft.params.val.length
      | .Err .TooManyResults => 1000 < ft.results.val.length
      | .Err _ => False ⦄ := by
  unfold code.check_func_type
  simp only [limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS]
  step*

/-- Pushing a resolved descriptor has exactly the shared stack primitive's
    effect, with no intermediate runtime vector. -/
theorem code.push_results.spec (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (ts : List types.ValueType)
    (hts : Wasm2.resolve env view = some ts)
    (hcap : st.vals.val.length + ts.length ≤ Usize.max) :
    code.push_results st env view ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = st.vals.val ++ ts.map code.StackType.Val ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨r, hr, ht⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases r with
  | Err e => simp [hts] at ht
  | Ok n =>
    obtain ⟨ts', he, hn⟩ := ht
    have heq : ts' = ts := by simpa [hts] using he.symm
    subst ts'
    unfold code.push_results
    rw [hr]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step
    split
    · scalar_tac
    · cases view with
      | Empty => simp_all [Wasm2.resolve]
      | One t =>
        simp [Wasm2.resolve] at hts
        subst ts
        step*
        all_goals simp_all
      | «Type» index part =>
        by_cases hi : index.val < env.types.val.length
        · cases part <;> simp [Wasm2.resolve, List.getElem?_eq_getElem hi] at hts
          all_goals subst ts
          all_goals step*
          all_goals simp_all [alloc.vec.Vec.deref]
        · simp [Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

/-- Popping a concrete suffix through a descriptor consumes the signature in
    reverse operand order and preserves control frames and cursor. -/
theorem code.pop_results.concrete (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (ts : List types.ValueType) (pre : List code.StackType)
    (hts : Wasm2.resolve env view = some ts)
    (hvals : st.vals.val = pre ++ ts.map code.StackType.Val)
    (hbase : (Control.base st).val ≤ pre.length) :
    code.pop_results st env view ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = pre ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  cases view with
  | Empty =>
    simp [Wasm2.resolve] at hts
    subst ts
    simp [code.pop_results, List.map_nil, List.append_nil] at hvals ⊢
    exact hvals
  | One t =>
    simp [Wasm2.resolve] at hts
    subst ts
    unfold code.pop_results
    step with code.pop_with_type.concrete st pre t (by simpa using hvals) hbase
    step*
  | «Type» index part =>
    by_cases hi : index.val < env.types.val.length
    · cases part <;> simp [Wasm2.resolve, List.getElem?_eq_getElem hi] at hts
      all_goals subst ts
      all_goals unfold code.pop_results
      all_goals step*
      all_goals simp_all [alloc.vec.Vec.deref]
    · simp [Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

/-- At an unreachable frame base, every resolved signature is consumed without
    fabricating a concrete operand vector or changing the state. -/
theorem code.pop_results.polymorphic (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (ts : List types.ValueType)
    (hts : Wasm2.resolve env view = some ts)
    (hbase : alloc.vec.Vec.len st.vals = Control.base st)
    (hpoly : Control.polymorphic st = true) :
    code.pop_results st env view = .ok (.Ok (), st) := by
  have hs : code.pop_results st env view ⦃ r => r = (.Ok (), st) ⦄ := by
    cases view with
    | Empty => simp [code.pop_results]
    | One t =>
      simp [code.pop_results, code.pop_with_type.polymorphic st t hbase hpoly,
        core.result.Result.Insts.CoreOpsTry.branch]
    | «Type» index part =>
      by_cases hi : index.val < env.types.val.length
      · unfold code.pop_results
        step
        split
        · scalar_tac
        · cases part <;> step
          all_goals simp [code.pop_types.polymorphic st _ hbase hpoly]
      · simp [Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts
  obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

end Itasca
