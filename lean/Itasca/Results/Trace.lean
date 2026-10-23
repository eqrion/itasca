import Itasca.Wasm2.Trace.Correspondence
import Itasca.Profile.EntryTrace

/-!
# Callback traces

Results relating the operator callbacks a recording visitor observes to the bytes and typing of
the validated body, for either profile. Body traces identify operator hooks, their order, state
snapshots, and immediates (float bits, branch-table labels, block signatures, and SIMD
immediates). Entry traces also cover the function-start callback. An observed rejecting callback
is included and is last.

Traces cover only executions that return. They do not specify full traces of rejected modules or
an exact error for every malformed input.
-/

open Aeneas Aeneas.Std

namespace Itasca

open VisitorTrace

/-- Every returned execution of `code.validate_body_with` has an observed callback trace
with exact byte provenance. A rejected final `br_table` may leave a partial vector, and no callback
follows an observed rejecting callback. No valid-input or total-callback premise is needed. -/
theorem code.validate_body_with.trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (v v' : V) (result : BodyResult)
    (run : code.validate_body_with visitor data env ctx index profile v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize observations result :=
  Wasm2.CallbackTrace.body_trace visitor observe records data env ctx index profile v v' result run

/-- An accepted run yields an `AcceptedBody` trace. The trace and the body's typing derivation
describe the same syntax, by uniqueness of the independent byte grammar. -/
theorem code.validate_body_with.trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (v v' : V)
    (run : code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.AcceptedBody profile data env ctx index observations :=
  Wasm2.CallbackTrace.body_trace_sound visitor observe records data env ctx index profile v v' run

/-- Independently encoded and typed bodies force every accepting recording visitor to accept and
to produce an `AcceptedBody` trace, within the documented resource bounds. No successful run is
assumed. -/
theorem code.validate_body_with.trace_complete {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (accepts : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (environment : Profile.EnvironmentWithinLimits env)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (body : Wasm2.Validated profile data env ctx.locals index) (v : V) :
    ∃ v' observations,
      code.validate_body_with visitor data env ctx index profile v = .ok (.Ok (), v') ∧
      observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.AcceptedBody profile data env ctx index observations :=
  Wasm2.CallbackTrace.body_trace_complete visitor observe records accepts data env ctx index profile
    environment size body v

/-- Wrapping a visitor with `instrument` keeps the result and the underlying visitor state of any
returned execution, and the added log satisfies `BodyTrace`. -/
theorem code.validate_body_with.instrument_trace {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (v : V) (log : List Observation) (result : BodyResult) (v' : V)
    (run : code.validate_body_with visitor data env ctx index profile v = .ok (result, v')) :
    ∃ added,
      code.validate_body_with (instrument visitor) data env ctx index profile (v, log) =
        .ok (result, (v', log ++ added)) ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize added result :=
  Wasm2.CallbackTrace.instrument_body_trace visitor data env ctx index profile v log result v' run

/-- The concrete `recorder` visitor terminates with a `BodyTrace` on arbitrary input bytes,
including malformed instructions and reserved opcodes. -/
theorem code.validate_body_with.recorder_total (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) : ∃ result observations,
    code.validate_body_with recorder data env ctx index profile [] =
      .ok (result, observations) ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize observations result :=
  Wasm2.CallbackTrace.recorder_body_total data env ctx index profile

/-- The concrete `recorder` visitor accepts an independently encoded, typed body and visits every
instruction, with all entries of every branch table in order. -/
theorem code.validate_body_with.recorder_complete (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (environment : Profile.EnvironmentWithinLimits env)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (body : Wasm2.Validated profile data env ctx.locals index) : ∃ observations,
    code.validate_body_with recorder data env ctx index profile [] =
      .ok (.Ok (), observations) ∧
      Wasm2.CallbackTrace.AcceptedBody profile data env ctx index observations := by
  obtain ⟨observations, added, run, equal, trace⟩ :=
    Wasm2.CallbackTrace.body_trace_complete recorder id recorder_records recorder_accepts data env
      ctx index profile environment size body []
  simp only [id_eq, List.nil_append] at equal
  exact ⟨observations, run, equal ▸ trace⟩

/-- A recording visitor that accepts an entry observes a function-start event followed by exactly
the independently encoded, typed operators of that entry. There is no termination or acceptance
hypothesis on other callback runs. -/
theorem module.validate_code_entry_with.trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List VisitorTrace.Observation) (hrecords : VisitorTrace.Records visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (index finish : Usize)
    (v v' : V) (hbound : CodeEntry.Bounds env) (profile : ValidationProfile)
    (hresults : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (h : module.validate_code_entry_with visitor data pos env index profile v = .ok (.Ok finish, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CodeEntry.AcceptedTrace profile data env index pos finish observations :=
  (module.validate_code_entry_with.witness_profile visitor data pos env index finish v v' hbound
    profile h).some.trace_sound observe hrecords hresults

end Itasca
