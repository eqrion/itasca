import Itasca.Wasm1.Invariant
import Itasca.Handler.RawControl

open Aeneas Aeneas.Std

namespace Itasca.Wasm1


theorem State.start (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    State data env ctx bt (Body.initial bt) := by
  apply State.running (Body.initial bt) [] (Wasm1.Frames.Saved.fresh (Body.initial bt) .body bt)
  · constructor <;> simp [Body.initial, hsize]
  · apply Wasm1.Frames.Open.start _ (EnvTranslation.context_wf env ctx)
    · rfl
    · rfl
  · rfl
  · simpa [Wasm1.Frames.trace, Wasm1.Frames.Saved.trace, Wasm1.Frames.Saved.fresh,
      Wasm1.Frames.Form.opening, Body.initial] using
      Consumed.nil (data := data) 0#usize (by simp)

theorem State.pending {data env ctx bt st} (h : State data env ctx bt st)
    (hctrls : st.ctrls.val ≠ []) (hpos : st.pos.val < data.length)
    (next : Usize) (hnext : next.val = st.pos.val + 1) :
    ∃ p : Pending data env ctx bt { st with pos := next }, p.start = st.pos := by
  cases h with
  | closed ops tokens bounds hc _ _ _ _ => exact False.elim (hctrls hc)
  | running parents current bounds hopen hbody hconsumed =>
    exact ⟨⟨st.pos, parents, current, bounds.size, hopen, hbody, hconsumed,
      hpos, hnext, bounds.vals, bounds.ctrls⟩, rfl⟩

def Steps {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (bt : code.BlockType) : Prop :=
  ∀ st (p : Pending data env ctx bt st) v,
    code.step visitor st data env ctx (data.val[p.start.val]'p.inbounds) v ⦃ r =>
      r.1 = .Ok () → p.After r.2.1 ⦄

theorem Steps.contract {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hsteps : Steps visitor data env ctx bt) :
    Body.StepContract visitor data env ctx (fun _ st => State data env ctx bt st) := by
  intro st v hi hc hp next hn
  obtain ⟨p, hstart⟩ := hi.pending hc hp next hn
  simpa only [hstart, Pending.After] using hsteps { st with pos := next } p v

/-- Acceptance without the additional version profile. -/
def Validated (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) : Prop := ∃ ops, BodyEncoding data ops ∧ FunctionTyped env ctx bt ops

/-- Acceptance has independent binary provenance and generated declarative body typing. -/
def Profiled (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) : Prop := ∃ ops, BodyEncoding data ops ∧ FunctionTyped env ctx bt ops ∧
    Wasm1.Instructions (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt) ops

end Itasca.Wasm1

namespace Itasca

/-- The implementation initializes one result only for a singleton result list.
Keeping that exact behavior here makes the termination result unconditional. -/
theorem code.validate_body_with.of_wasm1_steps {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hbt : Body.initialBlockType ctx.results.val = bt)
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
    have heq : Body.initialBlockType (alloc.vec.Vec.deref ctx.results).val = bt := by
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

/-- The public typing contract projects from the shared profile invariant. -/
theorem code.validate_body_with.of_wasm_steps {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hbt : Body.initialBlockType ctx.results.val = bt)
    (hsteps : Wasm1.Steps visitor data env ctx bt) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Wasm1.Validated data env ctx bt ⦄ := by
  apply WP.spec_mono (code.validate_body_with.of_wasm1_steps visitor data env ctx bt hbt hsteps v)
  rintro r hr hsuccess
  obtain ⟨ops, hb, ht, _⟩ := hr hsuccess
  exact ⟨ops, hb, ht⟩

end Itasca
