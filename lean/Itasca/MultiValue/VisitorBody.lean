import Itasca.MultiValue.VisitorStep
import Itasca.MultiValue.VisitorTotal
import Itasca.MultiValue.ScalarComplete
import Itasca.MultiValue.Soundness
import Itasca.MultiValue.Complete

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.MultiValue.Visitor

def bodyObserve {V : Type} :
    ControlFlow (V × multi_value.State) (core.result.Result Unit error.OpError × V) →
    ControlFlow multi_value.State (core.result.Result Unit error.OpError)
  | .cont (_, s) => .cont s
  | .done (r, _) => .done r

def bodyGood {V : Type} (cf :
    ControlFlow (V × multi_value.State) (core.result.Result Unit error.OpError × V)) : Prop :=
  match cf with
  | .cont _ => True
  | .done (r, _) => r = .Ok ()

abbrev body {V : Type} (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) (st : multi_value.State) :=
  multi_value.validate_body_with_loop.body visitor data env.types env.imports env.globals env.exports
    env.elements env.start env.func_type_indices env.func_types env.table_types env.mem_types
    env.global_types env.num_imported_funcs env.num_imported_globals ctx index v st

set_option maxHeartbeats 2000000 in
/-- Each successful body iteration transfers to an accepting visitor with the
same validator state. Only the locals component of the scalar context matters. -/
theorem body.transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (data : Slice U8) (env : module.Env) (ctx ctx' : code.Context)
    (hlocals : ctx.locals = ctx'.locals) (index : U32) (st : multi_value.State)
    (v : V) (w : W) (cf)
    (h : body visitor data env ctx index v st = .ok cf) (hg : bodyGood cf) :
    ∃ cf', body replacement data env ctx' index w st = .ok cf' ∧
      bodyObserve cf' = bodyObserve cf := by
  unfold body multi_value.validate_body_with_loop.body multi_value.body_loop_loop.body at h ⊢
  simp only [alloc.vec.Vec.is_empty, bind_ok] at h ⊢
  split at h
  · rename_i he
    simp only [he, if_true]
    split at h
    · simp only [ok.injEq] at h
      subst cf
      simp [bodyGood] at hg
    · rename_i hp
      simp only [ok.injEq] at h
      subst cf
      exact ⟨.done (.Ok (), w), by simp [hp], rfl⟩
  · rename_i he
    simp only [he, if_false]
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      subst cf
      simp [bodyGood] at hg
    | Ok pair =>
      obtain ⟨opcode, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨⟨r, s, v'⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        subst cf
        simp [bodyGood] at hg
      | Ok u =>
        cases u
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        subst cf
        obtain ⟨w', hw⟩ := step_transfer visitor replacement ha data env ctx ctx'
          hlocals index opcode { core := { st.core with pos } } s v w v' hs
        exact ⟨.cont (w', s), by simp [hw, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩

end Itasca.MultiValue.Visitor

namespace Itasca

open MultiValue.Visitor

/-- Visitor replacement preserves an accepted body loop. Structural progress is
obtained from the accepting replacement, so the source needs no totality premise. -/
theorem multi_value.validate_body_with_loop.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : FullVisitor.Accepts replacement) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (hlocals : ctx.locals = ctx'.locals) (index : U32)
    (st : multi_value.State) (v : V) (w : W) (v' : V)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Control.Shape st.core)
    (halign : st.blocks.val.length = st.core.ctrls.val.length)
    (hbound : st.blocks.val.length ≤ st.core.pos.val + 1)
    (h : multi_value.validate_body_with_loop visitor data env.types env.imports env.globals
      env.exports env.elements env.start env.func_type_indices env.func_types env.table_types
      env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals ctx index v st =
      .ok (.Ok (), v')) :
    ∃ w', multi_value.validate_body_with_loop replacement data env.types env.imports env.globals
      env.exports env.elements env.start env.func_type_indices env.func_types env.table_types
      env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals ctx' index w st =
      .ok (.Ok (), w') := by
  generalize hn : Usize.max - st.core.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v w with
  | h n ih =>
    unfold multi_value.validate_body_with_loop multi_value.body_loop_loop at h ⊢
    rw [loop] at h ⊢
    simp only [Std.uncurry] at h ⊢
    obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases cf with
    | done pair =>
      obtain ⟨r, v1⟩ := pair
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨cf, hw, ho⟩ := body.transfer visitor replacement ha data env ctx ctx' hlocals
        index st v w _ hb rfl
      simp only [MultiValue.Visitor.body, multi_value.validate_body_with_loop.body] at hw
      rw [hw]
      cases cf with
      | cont p => simp [bodyObserve] at ho
      | done p =>
        obtain ⟨r, w'⟩ := p
        simp only [bodyObserve, ControlFlow.done.injEq] at ho
        subst r
        exact ⟨w', by simp⟩
    | cont pair =>
      obtain ⟨v1, s⟩ := pair
      obtain ⟨cf, hw, ho⟩ := body.transfer visitor replacement ha data env ctx ctx' hlocals
        index st v w _ hb trivial
      have hp := multi_value.validate_body_with_loop.body_total replacement ha.toTotal
        data env ctx' index st w hdata hs halign hbound
      simp only [MultiValue.Visitor.body, multi_value.validate_body_with_loop.body] at hw
      simp only [multi_value.validate_body_with_loop.body] at hp
      rw [hw, WP.spec_ok] at hp
      rw [hw]
      cases cf with
      | done p => simp [bodyObserve] at ho
      | cont p =>
        obtain ⟨w1, s'⟩ := p
        simp only [bodyObserve, ControlFlow.cont.injEq] at ho
        subst s'
        obtain ⟨hinv, hdecr⟩ := hp
        dsimp only at hinv hdecr
        obtain ⟨w', hw'⟩ := ih (Usize.max - s.core.pos.val) (by omega) s v1 w1
          hinv.1 hinv.2.1 hinv.2.2 ht rfl
        exact ⟨w', by simpa only [bind_ok, multi_value.validate_body_with_loop, multi_value.body_loop_loop, Std.uncurry] using hw'⟩

/-- The public size guard, signature checks, and shared initialization preserve
successful execution under accepting callback replacement. -/
theorem multi_value.validate_body_with.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : FullVisitor.Accepts replacement) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (hlocals : ctx.locals = ctx'.locals) (index : U32)
    (v : V) (w : W) (v' : V)
    (h : multi_value.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    ∃ w', multi_value.validate_body_with replacement data env ctx' index w = .ok (.Ok (), w') := by
  unfold multi_value.validate_body_with multi_value.validate_body_with_profile at h ⊢
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h
  · simp only [hsize, if_false] at h ⊢
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hi : multi_value.initial_state env ctx' index .MultiValue =
        multi_value.initial_state env ctx index .MultiValue := rfl
    rw [hi, hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok st =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, multi_value.body_loop] at h ⊢
      have hp := multi_value.initial_state.multi_value_total env ctx index
      rw [hr, WP.spec_ok] at hp
      exact multi_value.validate_body_with_loop.accepted_transfer visitor replacement ha
        data env ctx ctx' hlocals index st v w v' (by scalar_tac) hp.1 hp.2.1 hp.2.2 h

end Itasca
