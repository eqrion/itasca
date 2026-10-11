import Itasca.Body.CoreInvariant

open Aeneas Aeneas.Std

namespace Itasca.Core

theorem State.start (data : Slice U8) (tokens : List Token) (ctx : code.Context)
    (bt : code.BlockType) (hbytes : Rest data 0#usize tokens)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    State data tokens ctx bt (Body.initial bt) := by
  apply State.running (Body.initial bt) [] (Frames.Saved.fresh (Body.initial bt) .body bt) tokens
  · constructor <;> simp [Body.initial, hsize]
  · apply Frames.Open.start _ (functionContext_wf ctx)
    · rfl
    · rfl
  · rfl
  · exact hbytes
  · simp [Frames.trace, Frames.Saved.trace, Frames.Saved.fresh, Frames.Form.opening]

/-- An active validator state and the next opcode expose exactly one pending
core token, without assuming its typing or control structure is valid. -/
theorem State.pending {data tokens ctx bt st} (h : State data tokens ctx bt st)
    (hctrls : st.ctrls.val ≠ []) (hpos : st.pos.val < data.length)
    (next : Usize) (hnext : next.val = st.pos.val + 1) :
    ∃ token, ∃ _p : Pending data tokens ctx bt { st with pos := next } token,
      data.val[st.pos.val] = token.opcode := by
  cases h with
  | closed _ _ _ _ hc _ _ _ _ => exact False.elim (hctrls hc)
  | running parents current remaining bounds hopen hbody hrest htrace =>
      cases hrest with
      | nil pos heq => omega
      | @cons pos finish token rest hat htail =>
          refine ⟨token, ⟨st.pos, finish, parents, current, rest, bounds.size,
            hopen, hbody, hat, htail, htrace, hnext, bounds.vals, bounds.ctrls⟩, ?_⟩
          exact hat.opcode.choose_spec

def Steps {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (tokens : List Token) (env : module.Env) (ctx : code.Context) (bt : code.BlockType) : Prop :=
  ∀ st token (p : Pending data tokens ctx bt st token) v,
    code.step visitor st data env ctx token.opcode v ⦃ r =>
      r.1 = .Ok () → State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄

theorem Steps.contract {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (tokens : List Token) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hsteps : Steps visitor data tokens env ctx bt) :
    Body.StepContract visitor data env ctx (fun _ st => State data tokens ctx bt st) := by
  intro st v hi hc hp next hn
  obtain ⟨token, p, hbyte⟩ := hi.pending hc hp next hn
  rw [hbyte]
  apply WP.spec_mono (hsteps { st with pos := next } token p v)
  intro r hr hok
  obtain ⟨hs, hpos⟩ := hr hok
  exact ⟨hs, by simpa [hpos] using p.next_ge, by simpa [hpos] using p.encoded.span.2⟩

/-- The final property is stated only in the local binary relation and the
generated declarative typing judgment, not in terms of the validator itself. -/
def Validated (data : Slice U8) (ctx : code.Context) (bt : code.BlockType) : Prop :=
  ∃ ops, BodyEncoding data ops ∧ FunctionTyped ctx bt ops

end Itasca.Core

namespace Itasca

/-- Composition through the actual public entry point. The next integration
layer discharges `Core.Steps` for all tokens in the documented profile. -/
theorem code.validate_body_with.of_core_steps {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (tokens : List Core.Token) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (hresults : ctx.results.val = Control.results bt)
    (hbytes : Core.Rest data 0#usize tokens)
    (hsteps : Core.Steps visitor data tokens env ctx bt) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Core.Validated data ctx bt ⦄ := by
  apply code.validate_body_with.spec visitor data env ctx bt hresults
    (fun _ st => Core.State data tokens ctx bt st) (fun _ => Core.Validated data ctx bt)
    (hsteps.contract visitor data tokens env ctx bt)
  · intro st v hi hc hp
    obtain ⟨ops, hbody, htyped⟩ := hi.finished hc hp
    exact ⟨ops, ⟨tokens, hbytes, hbody⟩, htyped⟩
  · exact Core.State.start data tokens ctx bt hbytes

end Itasca
