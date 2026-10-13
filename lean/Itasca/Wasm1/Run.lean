import Itasca.Wasm1.Invariant
import Itasca.Handler.RawControl

/-!
# Wasm 1.0 body runs

Turns per-step contracts into a result about `code.validate_body_with`. `Wasm1.Steps` says that
`code.step` takes a `Wasm1.Pending` state to its `After` state, and `Wasm1.State.start` shows the
initial loop state satisfies the invariant. `code.validate_body_with.of_wasm1_steps` and
`code.validate_body_with.of_wasm_steps` conclude `Wasm1.Profiled` and `Wasm1.Validated` for
accepted bodies.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- The initial loop state satisfies the body invariant when the body fits the size cap. -/
theorem State.start (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    State data env ctx bt (Wasm1.Loop.initial bt) := by
  apply State.running (Wasm1.Loop.initial bt) [] (Wasm1.Frames.Saved.fresh (Wasm1.Loop.initial bt) .body bt)
  · constructor <;> simp [Wasm1.Loop.initial, hsize]
  · apply Wasm1.Frames.Open.start _ (EnvTranslation.context_wf env ctx)
    · rfl
    · rfl
  · rfl
  · simpa [Wasm1.Frames.trace, Wasm1.Frames.Saved.trace, Wasm1.Frames.Saved.fresh,
      Wasm1.Frames.Form.opening, Wasm1.Loop.initial] using
      Consumed.nil (data := data) 0#usize (by simp)

/-- A running state with an open control frame and an unread byte yields a pending step. -/
theorem State.pending {data env ctx bt st} (h : State data env ctx bt st)
    (hctrls : st.ctrls.val ≠ []) (hpos : st.pos.val < data.length)
    (next : Usize) (hnext : next.val = st.pos.val + 1) :
    ∃ p : Pending data env ctx bt { st with pos := next }, p.start = st.pos := by
  cases h with
  | closed ops tokens bounds hc _ _ _ _ => exact False.elim (hctrls hc)
  | running parents current bounds hopen hbody hconsumed =>
    exact ⟨⟨st.pos, parents, current, bounds.size, hopen, hbody, hconsumed,
      hpos, hnext, bounds.vals, bounds.ctrls⟩, rfl⟩

/-- Every `code.step` call from a pending state, on any visitor state, either rejects or reaches
the state `Pending.After`. -/
def Steps {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (bt : code.BlockType) : Prop :=
  ∀ st (p : Pending data env ctx bt st) v,
    code.step visitor st data env ctx (data.val[p.start.val]'p.inbounds) v ⦃ r =>
      r.1 = .Ok () → p.After r.2.1 ⦄

/-- `Wasm1.Steps` gives the step contract of the shared loop `code.body_loop_loop` for the
invariant `Wasm1.State`. -/
theorem Steps.contract {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hsteps : Steps visitor data env ctx bt) :
    Wasm1.Loop.StepContract visitor data env ctx (fun _ st => State data env ctx bt st) := by
  intro st v hi hc hp next hn
  obtain ⟨p, hstart⟩ := hi.pending hc hp next hn
  simpa only [hstart, Pending.After] using hsteps { st with pos := next } p v

/-- The body bytes encode an instruction list with generated declarative body typing. -/
def Validated (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) : Prop := ∃ ops, BodyEncoding data ops ∧ FunctionTyped env ctx bt ops

/-- `Wasm1.Validated` together with the Wasm 1.0 profile on the instruction list. -/
def Profiled (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) : Prop := ∃ ops, BodyEncoding data ops ∧ FunctionTyped env ctx bt ops ∧
    Wasm1.Instructions (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt) ops

end Itasca.Wasm1

namespace Itasca

/-- Accepted executions of `code.validate_body_with` satisfy `Wasm1.Profiled`, given the step
contract. The hypothesis `hbt` matches the extracted initial block type, which carries a result
only for a singleton result list. -/
theorem code.validate_body_with.of_wasm1_steps {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hbt : Wasm1.Loop.initialBlockType ctx.results.val = bt)
    (hsteps : Wasm1.Steps visitor data env ctx bt) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Wasm1.Profiled data env ctx bt ⦄ := by
  simp only [code.validate_body_with.eq_model]
  unfold code.validate_body_with_model
  dsimp only
  split
  · simp [WP.spec_ok]
  · rename_i hsize
    rw [code.start_function.raw_spec]
    have heq : Wasm1.Loop.initialBlockType (alloc.vec.Vec.deref ctx.results).val = bt := by
      simpa [alloc.vec.Vec.deref] using hbt
    rw [heq]
    simp only [bind_ok]
    apply code.validate_body_with_loop.spec visitor data env ctx
      (fun _ st => Wasm1.State data env ctx bt st) (fun _ => Wasm1.Profiled data env ctx bt)
      (hsteps.contract visitor data env ctx bt)
    · intro st w hi hc hp
      exact hi.finished hc hp
    · apply Wasm1.State.start
      scalar_tac

/-- Accepted executions of `code.validate_body_with` satisfy `Wasm1.Validated`. This projects
`code.validate_body_with.of_wasm1_steps`. -/
theorem code.validate_body_with.of_wasm_steps {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hbt : Wasm1.Loop.initialBlockType ctx.results.val = bt)
    (hsteps : Wasm1.Steps visitor data env ctx bt) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Wasm1.Validated data env ctx bt ⦄ := by
  apply WP.spec_mono (code.validate_body_with.of_wasm1_steps visitor data env ctx bt hbt hsteps v)
  rintro r hr hsuccess
  obtain ⟨ops, hb, ht, _⟩ := hr hsuccess
  exact ⟨ops, hb, ht⟩

end Itasca
