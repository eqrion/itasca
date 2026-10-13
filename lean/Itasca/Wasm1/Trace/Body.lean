import Itasca.Wasm1.Trace.Step
import Itasca.Wasm1.Visitor.Refinement
import Itasca.Wasm1.Visitor.Lift
import Itasca.Binary.Wasm1.EncodingUnique

/-!
# Wasm 1.0 body traces

For a visitor that records its callbacks (`Records`), `code.validate_body_with.trace` gives
every returned execution of `code.validate_body_with` a byte-accurate callback trace.
`trace_sound` and `trace_complete` relate accepted traces (`AcceptedBody`) to the independent
encoding and the generated typing of the body, and `recorder_total` and `recorder_complete` apply
this to the concrete `recorder` visitor.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- Every callback in the trace accepted, and the callbacks spell a complete body that is
independently encoded and SpecTec-typed, including all structural delimiters. -/
def AcceptedBody (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (observations : List Observation) : Prop :=
  AllAccepted observations ∧ ∃ tokens ops next,
    Completed data 0#usize observations tokens next ∧ next.val = data.length ∧
    Wasm1.BodyTokens tokens ops ∧ Wasm1.FunctionTyped env ctx bt ops

end Itasca.VisitorTrace

namespace Itasca

open VisitorTrace

/-- Every returned execution of `code.validate_body_with` has an observed callback trace with
exact byte provenance. A rejected final `br_table` may leave a partial vector, and no callback
follows an observed rejecting callback. -/
theorem code.validate_body_with.trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (hrecords : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (v v' : V) (result : BodyResult)
    (h : code.validate_body_with visitor data env ctx v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      BodyTrace data 0#usize observations result :=
  code.validate_body_with.trace_of_contract visitor observe data env ctx
    (VisitorTrace.steps visitor observe hrecords data env ctx _) v v' result h

/-- An accepted run yields an `AcceptedBody` trace. The trace and the body's typing derivation
describe the same syntax, by uniqueness of the independent byte grammar. -/
theorem code.validate_body_with.trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (hrecords : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v v' : V)
    (h : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      AcceptedBody data env ctx bt observations := by
  obtain ⟨observations, hlog, htrace⟩ := code.validate_body_with.trace
    visitor observe hrecords data env ctx v v' (.Ok ()) h
  obtain ⟨ha, tokens, next, hc, hend⟩ := htrace.accepted
  obtain ⟨ops, ⟨tokens', next', hb, hend', hsyntax⟩, htyped⟩ :=
    code.validate_body_with.wasm_sound visitor data env ctx bt hresults v v' h
  have hp : next' = next := UScalar.eq_of_val_eq (hend'.trans hend.symm)
  subst next'
  have ht := hc.encoded.unique hb
  subst tokens'
  exact ⟨observations, hlog, ha, tokens, ops, next, hc, hend, hsyntax, htyped⟩

/-- Independent Wasm 1.0 encoding and typing force every accepting recording visitor to accept
and to produce an `AcceptedBody` trace. No successful run is assumed. -/
theorem code.validate_body_with.trace_complete {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (hrecords : Records visitor observe)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType) (henv : Wasm1.Environment env)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm1.Body data env ctx bt) (v : V) :
    ∃ v' observations, code.validate_body_with visitor data env ctx v = .ok (.Ok (), v') ∧
      observe v' = observe v ++ observations ∧ AcceptedBody data env ctx bt observations := by
  obtain ⟨v', hrun⟩ := code.validate_body_with.wasm_complete visitor haccept
    data env ctx bt henv hresults hsize hbody v
  obtain ⟨observations, hlog, htrace⟩ := code.validate_body_with.trace_sound visitor observe
    hrecords data env ctx bt hresults v v' hrun
  exact ⟨v', observations, hrun, hlog, htrace⟩

/-- Wrapping a visitor with `instrument` keeps the result and the underlying visitor state of any
returned execution, and the added log satisfies `BodyTrace`. -/
theorem code.validate_body_with.instrument_trace {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (log : List Observation) (result : BodyResult) (v' : V)
    (h : code.validate_body_with visitor data env ctx v = .ok (result, v')) :
    ∃ added, code.validate_body_with (instrument visitor) data env ctx (v, log) =
      .ok (result, (v', log ++ added)) ∧ BodyTrace data 0#usize added result := by
  obtain ⟨added, hrun⟩ := code.validate_body_with.instrument_forward visitor data env ctx v log result v' h
  obtain ⟨observations, heq, ht⟩ := code.validate_body_with.trace (instrument visitor) Prod.snd
    (instrument_records visitor) data env ctx (v, log) (v', log ++ added) result hrun
  have he : added = observations := List.append_cancel_left heq
  exact ⟨added, hrun, he ▸ ht⟩

/-- The concrete `recorder` visitor terminates with a `BodyTrace` on arbitrary input bytes,
including malformed and unsupported instructions. -/
theorem code.validate_body_with.recorder_total (data : Slice U8) (env : module.Env)
    (ctx : code.Context) : ∃ result observations,
    code.validate_body_with recorder data env ctx [] = .ok (result, observations) ∧
      BodyTrace data 0#usize observations result := by
  obtain ⟨⟨result, observations⟩, hrun⟩ := code.validate_body_with.wasm_total
    recorder VisitorTrace.recorder_total data env ctx []
  obtain ⟨added, heq, ht⟩ := code.validate_body_with.trace recorder id recorder_records
    data env ctx [] observations result hrun
  simp only [id_eq, List.nil_append] at heq
  exact ⟨result, observations, hrun, heq ▸ ht⟩

/-- The concrete `recorder` visitor accepts an independently encoded, typed Wasm 1.0 body and
visits every instruction, with all entries of every branch table in order. -/
theorem code.validate_body_with.recorder_complete (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType) (henv : Wasm1.Environment env)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm1.Body data env ctx bt) : ∃ observations,
    code.validate_body_with recorder data env ctx [] = .ok (.Ok (), observations) ∧
      AcceptedBody data env ctx bt observations := by
  obtain ⟨observations, added, hrun, heq, ht⟩ := code.validate_body_with.trace_complete
    recorder id recorder_records recorder_accepts data env ctx bt henv hresults hsize hbody []
  simp only [id_eq, List.nil_append] at heq
  exact ⟨observations, hrun, heq ▸ ht⟩

end Itasca
