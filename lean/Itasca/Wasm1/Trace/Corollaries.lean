import Itasca.Wasm1.Trace.Body
import Itasca.Visitor.TraceProperties

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- The pure callback projection recovers the same independently encoded and typed body. -/
theorem AcceptedBody.project {data env ctx bt observations}
    (h : AcceptedBody data env ctx bt observations) :
    ∃ tokens ops next, VisitorTrace.project observations [] = (tokens, []) ∧
      Wasm1.Consumed data 0#usize tokens next ∧ next.val = data.length ∧
      Wasm1.BodyTokens tokens ops ∧ Wasm1.FunctionTyped env ctx bt ops := by
  obtain ⟨_, tokens, ops, next, hc, hn, hb, ht⟩ := h
  exact ⟨tokens, ops, next, hc.project, hc.encoded, hn, hb, ht⟩

end Itasca.VisitorTrace

namespace Itasca

open VisitorTrace

/-- A callback observed to reject during the public API is last; the result
contains that same visitor error and every preceding callback accepted. -/
theorem code.validate_body_with.trace_rejection_last {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (hrecords : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (v v' : V) (result : BodyResult)
    (h : code.validate_body_with visitor data env ctx v = .ok (result, v'))
    (before after : List Observation) (event : Event) (e : error.VisitError)
    (hlog : observe v' = observe v ++ (before ++ [⟨event, .Err e⟩] ++ after)) :
    after = [] ∧ result = .Err (.Visitor e) ∧ AllAccepted before := by
  obtain ⟨observations, ho, ht⟩ := code.validate_body_with.trace
    visitor observe hrecords data env ctx v v' result h
  have he : observations = before ++ [⟨event, .Err e⟩] ++ after :=
    List.append_cancel_left (ho.symm.trans hlog)
  rw [he] at ht
  exact ht.1.rejecting

/-- The body API never synthesizes an entry-level function-start callback. -/
theorem code.validate_body_with.trace_no_function_start {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (hrecords : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (v v' : V) (result : BodyResult)
    (h : code.validate_body_with visitor data env ctx v = .ok (result, v'))
    (observations : List Observation) (hlog : observe v' = observe v ++ observations)
    (frame : code.Context) (idx : U32) (first last : Usize) :
    Event.functionStart frame idx first last ∉ observations.map Observation.event := by
  obtain ⟨added, ho, ht⟩ := code.validate_body_with.trace
    visitor observe hrecords data env ctx v v' result h
  have he : added = observations := List.append_cancel_left (ho.symm.trans hlog)
  rw [he] at ht
  exact ht.no_function_start frame idx first last

/-- On arbitrary bytes the concrete recorder terminates; its pure projection
is an independently encoded instruction prefix with optional unfinished labels. -/
theorem code.validate_body_with.recorder_projection (data : Slice U8) (env : module.Env)
    (ctx : code.Context) : ∃ result observations tokens cursor pending,
    code.validate_body_with recorder data env ctx [] = .ok (result, observations) ∧
      project observations [] = (tokens, pending) ∧ Wasm1.Consumed data 0#usize tokens cursor ∧
      (result = .Ok () → pending = [] ∧ cursor.val = data.length) := by
  obtain ⟨result, observations, hr, ht⟩ := code.validate_body_with.recorder_total data env ctx
  obtain ⟨tokens, cursor, pending, hp, hc, hend⟩ := ht.project
  exact ⟨result, observations, tokens, cursor, pending, hr, hp, hc, hend⟩

/-- Accepted recorder output projects to the full generated-specification-typed body,
including structural delimiters, with no pending branch-table labels. -/
theorem code.validate_body_with.recorder_projection_sound (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (observations : List Observation)
    (h : code.validate_body_with recorder data env ctx [] = .ok (.Ok (), observations)) :
    AllAccepted observations ∧ ∃ tokens ops next,
      project observations [] = (tokens, []) ∧ Wasm1.Consumed data 0#usize tokens next ∧
      next.val = data.length ∧ Wasm1.BodyTokens tokens ops ∧ Wasm1.FunctionTyped env ctx bt ops := by
  obtain ⟨added, heq, ht⟩ := code.validate_body_with.trace_sound recorder id recorder_records
    data env ctx bt hresults [] observations h
  have he : observations = added := by simpa using heq
  subst added
  exact ⟨ht.1, ht.project⟩

/-- Independent Wasm 1.0 typing and encoding produce an accepting recorder trace
whose pure projection is a complete typed body, without a prior execution premise. -/
theorem code.validate_body_with.recorder_projection_complete (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType) (henv : Wasm1.Environment env)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm1.Body data env ctx bt) : ∃ observations tokens ops next,
    code.validate_body_with recorder data env ctx [] = .ok (.Ok (), observations) ∧
      AllAccepted observations ∧ project observations [] = (tokens, []) ∧
      Wasm1.Consumed data 0#usize tokens next ∧ next.val = data.length ∧
      Wasm1.BodyTokens tokens ops ∧ Wasm1.FunctionTyped env ctx bt ops := by
  obtain ⟨observations, hr, ht⟩ := code.validate_body_with.recorder_complete
    data env ctx bt henv hresults hsize hbody
  obtain ⟨tokens, ops, next, hp, hc, hn, hb, htyped⟩ := ht.project
  exact ⟨observations, tokens, ops, next, hr, ht.1, hp, hc, hn, hb, htyped⟩

end Itasca
