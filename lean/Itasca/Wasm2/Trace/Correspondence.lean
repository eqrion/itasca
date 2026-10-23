import Itasca.Wasm2.Trace.Step
import Itasca.Wasm2.Trace.BodyRefinement
import Itasca.Wasm2.Visitor.Body

/-!
# Callback traces of body validation

Trace results for `code.validate_body_with`. `body_trace` gives exact byte provenance for
every ordinary return, `body_trace_sound` shows that accepted callbacks spell an independently
encoded, SpecTec-typed body (`AcceptedBody`), and `body_trace_complete` shows that every such body
forces the complete callback sequence. `instrument_body_trace` and `recorder_body_total` show that
instrumenting a visitor or running the recorder yields these traces without changing the
validation result. `Itasca/Results/Trace` states them as public results.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.CallbackTrace

open VisitorTrace

/-- The accepted callbacks spell the same independently encoded and SpecTec-typed body, with
indexed block signatures and declared references. For Wasm 1.0 the same tokens follow the Wasm 1.0
grammar and the body meets `Wasm1.Instructions`. -/
def AcceptedBody (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (observations : List Observation) : Prop :=
  AllAccepted observations ∧ ∃ ft tokens ops next,
    env.types.val[index.val]? = some ft ∧
    Completed data 0#usize observations tokens next ∧ next.val = data.length ∧
    BodyTokens tokens ops ∧ FunctionTyped env ctx.locals ft ops ∧
    DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops ∧
    (profile = .Wasm1 → Wasm1.Consumed data 0#usize tokens next ∧
      Wasm1.Instructions (functionContext env ctx.locals ft) ops)

end Itasca.Wasm2.CallbackTrace

namespace Itasca

open VisitorTrace

/-- Every ordinary body return has exact callback byte provenance. A rejected final table may be
partial; an observed rejecting callback is the last one recorded. No valid-input or total-callback
premise is needed. -/
theorem Wasm2.CallbackTrace.body_trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (v v' : V) (result : BodyResult)
    (run : code.validate_body_with visitor data env ctx index profile v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize observations result :=
  code.validate_body_with.trace_of_contract visitor observe data env ctx index profile
    (Wasm2.CallbackTrace.steps visitor observe records data env profile ctx.locals ctx index rfl)
    v v' result run

/-- Accepted callback syntax and generated typing refer to the same body, by uniqueness of the
independent byte grammar. -/
theorem Wasm2.CallbackTrace.body_trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (v v' : V)
    (run : code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.AcceptedBody profile data env ctx index observations := by
  obtain ⟨observations, log, trace⟩ := Wasm2.CallbackTrace.body_trace
    visitor observe records data env ctx index profile v v' (.Ok ()) run
  obtain ⟨accepted, tokens, next, chunks, endpos⟩ := trace.accepted
  obtain ⟨ft, ops, entry, ⟨tokens', next', bytes, endpos', hsyntax⟩, typed, declared, hwasm1⟩ :=
    code.validate_body_with.sound visitor data env ctx index profile v v' run
  have equal_pos : next' = next := UScalar.eq_of_val_eq (endpos'.trans endpos.symm)
  subst next'
  have equal_tokens := chunks.encoded.unique bytes
  subst tokens'
  refine ⟨observations, log, accepted, ft, tokens, ops, next, entry, chunks,
    endpos, hsyntax, typed, declared, fun hp => ?_⟩
  obtain ⟨⟨tokens1, next1, bytes1, endpos1, hsyntax1⟩, hinstr⟩ := hwasm1 hp
  have equal_pos1 : next1 = next := UScalar.eq_of_val_eq (endpos1.trans endpos.symm)
  subst next1
  have equal_tokens1 := chunks.encoded.unique bytes1.to_wasm2
  subst tokens1
  exact ⟨bytes1, hinstr⟩

/-- Independently encoded and typed bodies force a complete callback trace for accepting
recording visitors within the documented resource bounds. -/
theorem Wasm2.CallbackTrace.body_trace_complete {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (accepts : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (environment : Profile.EnvironmentWithinLimits env)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (body : Wasm2.Validated profile data env ctx.locals index) (v : V) :
    ∃ v' observations,
      code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v') ∧
      observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.AcceptedBody profile data env ctx index observations := by
  obtain ⟨v', run⟩ := code.validate_body_with.complete visitor accepts
    data env ctx index profile environment size body v
  obtain ⟨observations, log, trace⟩ := Wasm2.CallbackTrace.body_trace_sound
    visitor observe records data env ctx index profile v v' run
  exact ⟨v', observations, run, log, trace⟩

/-- Instrumenting an ordinary execution does not change its result or underlying visitor state.
The added observations satisfy byte provenance. -/
theorem Wasm2.CallbackTrace.instrument_body_trace {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (v : V)
    (log : List Observation) (result : BodyResult) (v' : V)
    (run : code.validate_body_with visitor data env ctx index profile v = .ok (result, v')) :
    ∃ added,
      code.validate_body_with (instrument visitor) data env ctx index profile (v, log) =
        .ok (result, (v', log ++ added)) ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize added result := by
  obtain ⟨added, instrumented⟩ := code.validate_body_with.instrument_forward
    visitor data env ctx index profile v log result v' run
  obtain ⟨observations, equal_log, trace⟩ := Wasm2.CallbackTrace.body_trace
    (instrument visitor) Prod.snd (instrument_records visitor) data env ctx index profile
    (v, log) (v', log ++ added) result instrumented
  have equal : added = observations := List.append_cancel_left equal_log
  exact ⟨added, instrumented, equal ▸ trace⟩

/-- The concrete recorder returns a byte-provenance trace on arbitrary input, including malformed
instructions and reserved opcodes. -/
theorem Wasm2.CallbackTrace.recorder_body_total (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) : ∃ result observations,
    code.validate_body_with recorder data env ctx index profile [] =
      .ok (result, observations) ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize observations result := by
  obtain ⟨⟨result, observations⟩, run⟩ := code.validate_body_with.total
    recorder VisitorTrace.recorder_total data env ctx index profile []
  obtain ⟨added, equal_log, trace⟩ := Wasm2.CallbackTrace.body_trace
    recorder id recorder_records data env ctx index profile [] observations result run
  simp only [id_eq, List.nil_append] at equal_log
  exact ⟨result, observations, run, equal_log ▸ trace⟩

end Itasca
