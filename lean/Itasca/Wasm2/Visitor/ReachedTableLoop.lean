import Itasca.Wasm2.Visitor.Step
import Itasca.Wasm2.Visitor.Total
import Itasca.Wasm2.Scalar.Complete
import Itasca.Wasm2.Soundness
import Itasca.Wasm2.Completeness
import Itasca.Wasm2.Visitor.BrTable

/-!
Sections, each formerly its own module: Transfer, Body, ReachedTableLoop.
-/

/-! ## Transfer -/

section

/-!
# Visitor transfer for the body loop

`body.transfer` shows that one successful iteration of the extracted body loop transfers to a
replacement visitor with accepting callbacks, with the same validator state. This lifts to the
whole loop (`code.body_loop_loop.accepted_transfer`) and to
`code.validate_body_with.accepted_transfer`, which includes the size guard and
initialization.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Wasm2.Visitor

/-- Drops the visitor state from the result of one body iteration. -/
def bodyObserve {V : Type} :
    ControlFlow (V × code.BodyState) (core.result.Result Unit error.OpError × V) →
    ControlFlow code.BodyState (core.result.Result Unit error.OpError)
  | .cont (_, s) => .cont s
  | .done (r, _) => .done r

/-- A body iteration result that continues or returns `Ok ()`. -/
def bodyGood {V : Type} (cf :
    ControlFlow (V × code.BodyState) (core.result.Result Unit error.OpError × V)) : Prop :=
  match cf with
  | .cont _ => True
  | .done (r, _) => r = .Ok ()

/-- One iteration of the extracted body loop. -/
abbrev body {V : Type} (visitor : code.OpVisitor V) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) (st : code.BodyState) :=
  code.body_loop_loop.body visitor data env ctx index v st

set_option maxHeartbeats 2000000 in
/-- Each successful body iteration transfers to an accepting visitor with the
same validator state. Only the locals component of the scalar context matters. -/
theorem body.transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (data : Slice U8) (env : metadata.Env) (ctx ctx' : code.Context)
    (hlocals : ctx.locals = ctx'.locals) (index : U32)
    (st : code.BodyState) (v : V) (w : W) (cf)
    (h : body visitor data env ctx index v st = .ok cf) (hg : bodyGood cf) :
    ∃ cf', body replacement data env ctx' index w st = .ok cf' ∧
      bodyObserve cf' = bodyObserve cf := by
  unfold body code.body_loop_loop.body at h ⊢
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
    simp only [he]
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
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        subst cf
        simp [bodyGood] at hg
      | Ok u =>
        cases u
        simp at h
        subst cf
        obtain ⟨w', hw⟩ := step_transfer visitor replacement ha data env ctx ctx'
          hlocals index opcode { core := { st.core with pos } } s v w v' hs
        exact ⟨.cont (w', s), by simp [hw], rfl⟩

end Itasca.Wasm2.Visitor

namespace Itasca

open Wasm2.Visitor

/-- Visitor replacement preserves an accepted body loop. Structural progress is
obtained from the accepting replacement, so the source needs no totality premise. -/
theorem code.body_loop_loop.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : FullVisitor.Accepts replacement) (data : Slice U8) (env : metadata.Env)
    (ctx ctx' : code.Context) (hlocals : ctx.locals = ctx'.locals) (index : U32)
     (st : code.BodyState) (v : V) (w : W) (v' : V)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Control.Shape st.core)
    (halign : st.blocks.val.length = st.core.ctrls.val.length)
    (hbound : st.blocks.val.length ≤ st.core.pos.val + 1)
    (h : code.body_loop_loop visitor data env ctx index v st =
      .ok (.Ok (), v')) :
    ∃ w', code.body_loop_loop replacement data env ctx' index w st =
      .ok (.Ok (), w') := by
  generalize hn : Usize.max - st.core.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v w with
  | h n ih =>
    unfold code.body_loop_loop at h ⊢
    rw [loop] at h ⊢
    simp only at h ⊢
    obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases cf with
    | done pair =>
      obtain ⟨r, v1⟩ := pair
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨cf, hw, ho⟩ := body.transfer visitor replacement ha data env ctx ctx' hlocals
        index st v w _ hb rfl
      simp only [Wasm2.Visitor.body] at hw
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
      have hp := code.body_loop_loop.body.total replacement ha.toTotal
        data env ctx' index st w hdata hs halign hbound
      simp only [Wasm2.Visitor.body] at hw
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
        exact ⟨w', by simpa only [bind_ok, code.body_loop_loop, Std.uncurry] using hw'⟩

/-- The public size guard, signature checks, and shared initialization preserve
successful execution under accepting callback replacement. -/
theorem code.validate_body_with.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : FullVisitor.Accepts replacement) (data : Slice U8) (env : metadata.Env)
    (ctx ctx' : code.Context) (hlocals : ctx.locals = ctx'.locals) (index : U32)
     (v : V) (w : W) (v' : V)
    (h : code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    ∃ w', code.validate_body_with replacement data env ctx' index w =
      .ok (.Ok (), w') := by
  unfold code.validate_body_with at h ⊢
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h
  · simp only [hsize, if_false] at h ⊢
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok st =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.body_loop] at h ⊢
      have hp := code.initial_state.total env index
      rw [hr, WP.spec_ok] at hp
      exact code.body_loop_loop.accepted_transfer visitor replacement ha
        data env ctx ctx' hlocals index st v w v' (by scalar_tac) hp.1 hp.2.1 hp.2.2 h

end Itasca

end

/-! ## Body -/

section

/-!
# Visiting body validation against the empty-visitor validator

Relates `code.validate_body_with`, the body validator with an arbitrary visitor, to the
empty-visitor validator `code.bodyCore`. `eq_core` identifies the empty-visitor run with
`code.bodyCore`, `accepted_erase` and `accepted_lift` give acceptance in both directions, and
`sound` and `complete` lift soundness and completeness to arbitrary accepting visitors.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The empty-visitor run of `code.validate_body_with` is `code.bodyCore`. -/
theorem code.validate_body_with.eq_core (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) :
    (do
      let (r, _) ← code.validate_body_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        data env ctx index ()
      .ok r) = code.bodyCore data env ctx.locals ctx.results index := by
  unfold code.validate_body_with code.initial_state code.bodyCore
  simp only [Std.bind_assoc]
  split
  · simp
  · simp only [Std.bind_assoc]
    congr 1
    funext i
    split
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp only [Std.bind_assoc]
      congr 1
      funext ft
      congr 1
      funext r
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        cases u
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
        rfl

/-- An accepted visiting body is accepted by the empty-visitor validator, for any result vector
of the scalar context. The source visitor needs no totality assumption. -/
theorem code.validate_body_with.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (results : alloc.vec.Vec wasm_types.ValueType) (v v' : V)
    (h : code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    code.bodyCore data env ctx.locals results index = .ok (.Ok ()) := by
  obtain ⟨w, hw⟩ := code.validate_body_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data env ctx
    ⟨ctx.locals, results⟩ rfl index v () v' h
  cases w
  rw [← code.validate_body_with.eq_core data env ⟨ctx.locals, results⟩]
  simp [hw]

/-- Accepting hooks preserve acceptance by the empty-visitor validator. The scalar context's
result vector does not constrain the signature selected by the type index. -/
theorem code.validate_body_with.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (results : alloc.vec.Vec wasm_types.ValueType) (v : V)
    (h : code.bodyCore data env ctx.locals results index = .ok (.Ok ())) :
    ∃ v', code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v') := by
  rw [← code.validate_body_with.eq_core data env ⟨ctx.locals, results⟩] at h
  obtain ⟨⟨r, w⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases w
  simp [Std.uncurry] at h
  subst r
  exact code.validate_body_with.accepted_transfer
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor visitor ha data env
    ⟨ctx.locals, results⟩ ctx rfl index () v () hr

/-- Arbitrary accepted visitors establish `Wasm2.Validated` for the profile, without a callback
totality premise. -/
theorem code.validate_body_with.sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (v v' : V)
    (h : code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    Wasm2.Validated data env ctx.locals index :=
  code.bodyCore.sound data env ctx.locals ctx.results index
    (code.validate_body_with.accepted_erase visitor data env ctx index _ v v' h)

/-- `Wasm2.Validated` bodies are accepted with accepting callbacks, subject to the
implementation limits. -/
theorem code.validate_body_with.complete {V : Type} (visitor : code.OpVisitor V)
    (ha : FullVisitor.Accepts visitor) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (henv : Profile.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm2.Validated data env ctx.locals index) (v : V) :
    ∃ v', code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v') :=
  code.validate_body_with.accepted_lift visitor ha data env ctx index ctx.results v
    (code.bodyCore.complete data env ctx.locals ctx.results index henv hsize hbody)

end Itasca

end

/-! ## ReachedTableLoop -/

section

namespace Itasca.Wasm2.Visitor
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The real Wasm 2 target loop terminates from a reached-state body contract.
The count/index measure includes the final default-target iteration. -/
theorem _root_.Itasca.code.branch_table_with_loop.total_on {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : metadata.Env)
     (count : U32)
    (inv : code.BodyState → V → Option Usize → U32 → Prop)
    (post : code.BodyState → V → Prop)
    (steps : ∀ st v arity index, index.val ≤ count.val → inv st v arity index →
      tableBody visitor data env count st v arity index ⦃ result =>
        match result with
        | .done out => out.1 = .Ok () → post out.2.1 out.2.2
        | .cont next => next.2.2.2.val ≤ count.val ∧ index.val < next.2.2.2.val ∧
            inv ⟨next.1⟩ next.2.1 next.2.2.1 next.2.2.2 ⦄)
    (st : code.BodyState) (v : V) (arity : Option Usize) (index : U32) (bound : index.val ≤ count.val) (initial : inv st v arity index) :
    code.branch_table_with_loop visitor st.core data env v count arity index ⦃ result =>
      result.1 = .Ok () → post result.2.1 result.2.2 ⦄ := by
  unfold code.branch_table_with_loop
  apply loop.spec_decr_nat (fun state => count.val-state.2.2.2.val)
    (fun state => state.2.2.2.val ≤ count.val ∧
      inv ⟨state.1⟩ state.2.1 state.2.2.1 state.2.2.2)
  · rintro ⟨core,value,current,index⟩ ⟨bound,held⟩
    dsimp only
    rw [tableBody_eq visitor data env count ⟨core⟩ value current index]
    apply WP.spec_mono (steps ⟨core⟩ value current index bound held)
    intro result resultPost
    cases result with
    | done output => exact resultPost
    | cont next =>
      exact ⟨⟨resultPost.1,resultPost.2.2⟩,by omega⟩
  · exact ⟨bound,initial⟩
end Itasca.Wasm2.Visitor

end
