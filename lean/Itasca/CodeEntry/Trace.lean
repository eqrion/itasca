import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.CodeEntry.Validation
import Itasca.Body.Trace.BytesDispatch

/-!
# Code entry traces

`CodeEntry.AcceptedTrace` ties an entry's independent code encoding, its generated typing and the
operator stream a recording visitor observed to one instruction tree. `Witness.trace_sound` builds
it from a `Witness`. `Itasca/Results/Trace` states it for a successful call of
`metadata.validate_code_entry_with`.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

open Visitor.Trace

/-- A `Witness` gives an `AcceptedTrace` of the observations the recording visitor added. The
function-start event and the body log align with the syntax used for the code entry typing
certificate. -/
theorem Witness.trace_sound {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish v v' }
    (w : Witness visitor data env index start finish v v' )
    (observe : V → List Observation) (hrecords : Records visitor observe) :
    ∃ observations, observe v' = observe v ++ observations ∧
      AcceptedTrace data env index start finish observations := by
  have haccepted := w.body_accepted
  obtain ⟨bodyObservations, hlog, accepted, ft, tokens, ops, next, hi, hc, hend, hsyntax, ht,
    hdeclared⟩ := Body.CallbackTrace.body_trace_sound visitor observe hrecords w.body env
      w.ctx w.typeIdx w.startedState v' haccepted
  have hlookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    rw [List.getElem?_eq_getElem w.type_lt, w.function_type]
  have hft : ft = w.ft := Option.some.inj (hi.symm.trans hlookup)
  subst ft
  have hbody : Body.BodyEncoding w.body ops :=
    ⟨tokens, next, hc.encoded, hend, hsyntax⟩
  have hstart := hrecords v (.functionStart w.ctx w.typeIdx w.bodyStart finish) (.Ok ())
    w.startedState w.function_start
  refine ⟨⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩ :: bodyObservations,
    ?_, w.typeIdx, w.groups, w.ctx, w.bodyStart, w.body, bodyObservations, tokens, ops, next,
    ⟨w.index_lt, w.index_type⟩,
    CodeEntry.code_encoding_of_parts w.header w.extent w.locals_bytes w.body_bytes hbody,
    CodeEntry.Typed.of_body hi w.context_locals ht hdeclared,
    w.locals_bound, ?_, w.body_bytes, rfl, accepted, hc, hend, hsyntax,
    w.content, w.size, w.header, w.extent, w.locals_bytes⟩
  · simpa [hstart, List.append_assoc] using hlog
  · exact ⟨w.type_lt, by simpa [w.function_type] using w.context_locals,
      by simpa [w.function_type] using w.context_results⟩

end Itasca.CodeEntry
