import Itasca.Visitor.VisitorStepTrace
import Itasca.Visitor.VisitorBodyRefinement
import Itasca.Visitor.VisitorBodyComplete
import Itasca.Binary.WasmBinaryUnique

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- An accepted trace spells exactly the complete independently encoded,
SpecTec-typed instruction body, including all structural delimiters. -/
def AcceptedBody (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (observations : List Observation) : Prop :=
  AllAccepted observations ∧ ∃ tokens ops next,
    Completed data 0#usize observations tokens next ∧ next.val = data.length ∧
    Wasm.BodyTokens tokens ops ∧ Wasm.FunctionTyped env ctx bt ops

end Itasca.VisitorTrace

namespace Itasca

open VisitorTrace

/-- Every ordinary public body return has exact observed callback byte
provenance. The final rejected instruction may leave a partial table vector;
an observed rejecting callback is retained and no callback follows it. -/
theorem code.validate_body_with.trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (hrecords : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (v v' : V) (result : BodyResult)
    (h : code.validate_body_with visitor data env ctx v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      BodyTrace data 0#usize observations result :=
  code.validate_body_with.trace_of_contract visitor observe data env ctx
    (VisitorTrace.steps visitor observe hrecords data env ctx _) v v' result h

/-- Accepted traces and declarative body typing refer to the same syntax,
using uniqueness of the independent byte grammar to align their witnesses. -/
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

/-- Independent Wasm 1.0 encoding and typing force acceptance and a complete
trace for every accepting recording visitor. No successful run is assumed. -/
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

/-- Instrument any ordinary returned execution without changing its result or
underlying visitor state; the added log satisfies the independent trace relation. -/
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

/-- The concrete recorder terminates and produces a valid trace on arbitrary
input bytes, including malformed and unsupported instructions. -/
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

/-- The concrete accepting recorder visits every instruction of an independently
encoded, typed Wasm 1.0 body, with all entries of every branch table in order. -/
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
