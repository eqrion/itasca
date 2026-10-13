import Itasca.Wasm2.Trace.Step
import Itasca.Wasm2.Trace.BodyRefinement
import Itasca.Wasm2.Visitor.Body

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.CallbackTrace

open VisitorTrace

/-- The accepted Core 2.0 callbacks spell the same independently encoded and
SpecTec-typed body, retaining indexed block signatures and declared references. -/
def AcceptedBody (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (observations : List Observation) : Prop :=
  AllAccepted observations ∧ ∃ ft tokens ops next,
    env.types.val[index.val]? = some ft ∧
    Completed data 0#usize observations tokens next ∧ next.val = data.length ∧
    BodyTokens tokens ops ∧ FunctionTyped env ctx.locals ft ops ∧
    DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops

end Itasca.MultiValue.CallbackTrace

namespace Itasca

open VisitorTrace

/-- Every ordinary Core 2.0 body return has exact callback byte provenance.
A rejected final table may be partial; an observed rejecting callback is retained
and no callback follows it. No valid-input or total-callback premise is needed. -/
theorem code.validate_multi_value_body_with.trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (v v' : V) (result : BodyResult)
    (run : code.validate_multi_value_body_with visitor data env ctx index v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      MultiValue.CallbackTrace.BodyTrace data 0#usize observations result :=
  code.validate_multi_value_body_with.trace_of_contract visitor observe data env ctx index
    (MultiValue.CallbackTrace.steps visitor observe records data env ctx.locals ctx index rfl)
    v v' result run

/-- Accepted callback syntax and generated typing refer to the same Core 2.0
body, by uniqueness of the independent byte grammar. -/
theorem code.validate_multi_value_body_with.trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v v' : V)
    (run : code.validate_multi_value_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      MultiValue.CallbackTrace.AcceptedBody data env ctx index observations := by
  obtain ⟨observations, log, trace⟩ := code.validate_multi_value_body_with.trace
    visitor observe records data env ctx index v v' (.Ok ()) run
  obtain ⟨accepted, tokens, next, chunks, endpos⟩ := trace.accepted
  obtain ⟨ft, ops, entry, ⟨tokens', next', bytes, endpos', hsyntax⟩, typed, declared⟩ :=
    code.validate_multi_value_body_with.wasm_sound visitor data env ctx index v v' run
  have equal_pos : next' = next := UScalar.eq_of_val_eq (endpos'.trans endpos.symm)
  subst next'
  have equal_tokens := chunks.encoded.unique bytes
  subst tokens'
  exact ⟨observations, log, accepted, ft, tokens, ops, next, entry, chunks,
    endpos, hsyntax, typed, declared⟩

/-- Independently encoded and typed Core 2.0 bodies force a complete callback
trace for accepting recording visitors within the documented resource bounds. -/
theorem code.validate_multi_value_body_with.trace_complete {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (accepts : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (environment : MultiValue.EnvironmentWithinLimits env)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (body : MultiValue.Validated data env ctx.locals index) (v : V) :
    ∃ v' observations,
      code.validate_multi_value_body_with visitor data env ctx index v = .ok (.Ok (), v') ∧
      observe v' = observe v ++ observations ∧
      MultiValue.CallbackTrace.AcceptedBody data env ctx index observations := by
  obtain ⟨v', run⟩ := code.validate_multi_value_body_with.wasm_complete visitor accepts
    data env ctx index environment size body v
  obtain ⟨observations, log, trace⟩ := code.validate_multi_value_body_with.trace_sound
    visitor observe records data env ctx index v v' run
  exact ⟨v', observations, run, log, trace⟩

/-- Instrument an ordinary Core 2.0 execution without changing its result or
underlying visitor state. The actual added observations satisfy byte provenance. -/
theorem code.validate_multi_value_body_with.instrument_trace {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v : V)
    (log : List Observation) (result : BodyResult) (v' : V)
    (run : code.validate_multi_value_body_with visitor data env ctx index v = .ok (result, v')) :
    ∃ added,
      code.validate_multi_value_body_with (instrument visitor) data env ctx index (v, log) =
        .ok (result, (v', log ++ added)) ∧
      MultiValue.CallbackTrace.BodyTrace data 0#usize added result := by
  obtain ⟨added, instrumented⟩ := code.validate_multi_value_body_with.instrument_forward
    visitor data env ctx index v log result v' run
  obtain ⟨observations, equal_log, trace⟩ := code.validate_multi_value_body_with.trace
    (instrument visitor) Prod.snd (instrument_records visitor) data env ctx index
    (v, log) (v', log ++ added) result instrumented
  have equal : added = observations := List.append_cancel_left equal_log
  exact ⟨added, instrumented, equal ▸ trace⟩

/-- The concrete recorder returns a byte-provenance trace on arbitrary Core 2.0
input, including malformed instructions and reserved opcodes. -/
theorem code.validate_multi_value_body_with.recorder_total (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) : ∃ result observations,
    code.validate_multi_value_body_with recorder data env ctx index [] = .ok (result, observations) ∧
      MultiValue.CallbackTrace.BodyTrace data 0#usize observations result := by
  obtain ⟨⟨result, observations⟩, run⟩ := code.validate_multi_value_body_with.wasm_total
    recorder VisitorTrace.recorder_total data env ctx index []
  obtain ⟨added, equal_log, trace⟩ := code.validate_multi_value_body_with.trace
    recorder id recorder_records data env ctx index [] observations result run
  simp only [id_eq, List.nil_append] at equal_log
  exact ⟨result, observations, run, equal_log ▸ trace⟩

end Itasca
