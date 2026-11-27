import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Body.Trace.BytesDispatch
import Itasca.CodeEntry.Trace

/-!
# Callback traces

Results relating the operator callbacks a recording visitor observes to the bytes and typing of
the validated body, for WebAssembly Core 2.0. Body traces identify operator hooks, their order, state
snapshots, and immediates (float bits, branch-table labels, block signatures, and SIMD
immediates). Entry traces also cover the function-start callback. An observed rejecting callback
is included and is last.

The four results cover arbitrary returning runs, accepted runs, completeness for
valid inputs with accepting callbacks, and accepted code-entry traces. Clients
provide an observation function satisfying `Records`; no particular logging
implementation is part of these statements. Recorder and instrumentation
corollaries live in Body/Trace/Acceptance.

Traces cover only executions that return. They do not specify full traces of rejected modules or
an exact error for every malformed input.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Visitor.Trace

/-- Every returned execution of `code.validate_body_with` has an observed callback trace
with exact byte provenance. A rejected final `br_table` may leave a partial vector, and no callback
follows an observed rejecting callback. No valid-input or total-callback premise is needed. -/
theorem code.validate_body_with.trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (index : U32)
     (v v' : V) (result : BodyResult)
    (run : code.validate_body_with visitor data env ctx index v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Body.CallbackTrace.BodyTrace data 0#usize observations result :=
  Body.CallbackTrace.body_trace visitor observe records data env ctx index v v' result run

/-- An accepted run yields an `AcceptedBody` trace. The trace and the body's typing derivation
describe the same syntax, by uniqueness of the independent byte grammar. -/
theorem code.validate_body_with.trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (index : U32)
     (v v' : V)
    (run : code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Body.CallbackTrace.AcceptedBody data env ctx index observations :=
  Body.CallbackTrace.body_trace_sound visitor observe records data env ctx index v v' run

/-- Independently encoded and typed bodies force every accepting recording visitor to accept and
to produce an `AcceptedBody` trace, within the documented resource bounds. No successful run is
assumed. -/
theorem code.validate_body_with.trace_complete {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (accepts : Visitor.Accepts visitor) (data : Slice U8) (env : metadata.CodeMetadata)
    (ctx : code.Context) (index : U32)
    (environment : CodeEntry.EnvironmentWithinLimits env)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (body : Body.Validated data env ctx.locals index) (v : V) :
    ∃ v' observations,
      code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v') ∧
      observe v' = observe v ++ observations ∧
      Body.CallbackTrace.AcceptedBody data env ctx index observations :=
  Body.CallbackTrace.body_trace_complete visitor observe records accepts data env ctx index
    environment size body v

/-- A recording visitor that accepts an entry observes a function-start event followed by exactly
the independently encoded, typed operators of that entry. There is no termination or acceptance
hypothesis on other callback runs. -/
theorem metadata.validate_code_entry_with.trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Visitor.Trace.Observation) (records : Visitor.Trace.Records visitor observe)
    (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata) (index finish : Usize)
    (v v' : V) (entry_bounds : CodeEntry.Bounds env)
    (accepted : metadata.validate_code_entry_with visitor data pos env index v = .ok (.Ok finish, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CodeEntry.AcceptedTrace data env index pos finish observations :=
  (metadata.validate_code_entry_with.witness visitor data pos env index finish v v' entry_bounds
     accepted).some.trace_sound observe records

end Itasca
