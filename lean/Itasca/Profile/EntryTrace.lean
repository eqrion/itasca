import Itasca.Profile.EntrySound
import Itasca.Wasm2.Trace.Correspondence

/-!
# Code entry traces

`CodeEntry.AcceptedTrace` ties an entry's independent code encoding, its generated typing and the
operator stream a recording visitor observed to one instruction tree. `Witness.trace_sound` builds
it from a `Witness`. `Itasca/Results/Trace` states it for a successful call of
`metadata.validate_code_entry_with`.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

open VisitorTrace

/-- The observations of an accepted entry come from a function-start event followed by body
operator events. The code bytes, generated typing and recorded operators share one instruction
tree. The start event uses module offsets, and operator states use offsets of the sliced body. -/
def AcceptedTrace (data : Slice U8) (env : metadata.Env)
    (index start finish : Usize) (observations : List Observation) : Prop :=
  ∃ (typeIdx : U32) (groups : List (U32 × wasm_types.ValueType)) (ctx : code.Context)
      (bodyStart : Usize) (body : Slice U8) (bodyObservations : List Observation)
      (tokens : List Wasm2.Token) (ops : List instr) (next : Usize),
    (∃ hi : index.val < env.func_type_indices.val.length,
      env.func_type_indices.val[index.val] = typeIdx) ∧
    ModuleBinary.At (Profile.CodeEncoding ) data start ⟨groups, ops⟩ finish ∧
    Profile.EntryTyped env typeIdx ⟨groups, ops⟩ ∧
    (ModuleLocals.declared groups).length ≤ limits.MAX_LOCALS.val ∧
    (∃ ht : typeIdx.val < env.types.val.length,
      ctx.locals.val = env.types.val[typeIdx.val].params.val ++ ModuleLocals.declared groups ∧
      ctx.results.val = env.types.val[typeIdx.val].results.val) ∧
    Wasm1.BytesAt data bodyStart body.val finish ∧
    observations = ⟨.functionStart ctx typeIdx bodyStart finish, .Ok ()⟩ :: bodyObservations ∧
    AllAccepted bodyObservations ∧
    Wasm2.CallbackTrace.Completed body 0#usize bodyObservations tokens next ∧
    next.val = body.length ∧ Wasm2.BodyTokens tokens ops ∧
    (∃ (content : Usize) (size : U32),
      Leb128.Decoded data start size content ∧
      finish.val = content.val + size.val ∧
      ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding)
        data content groups bodyStart)

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
    hdeclared⟩ := Wasm2.CallbackTrace.body_trace_sound visitor observe hrecords w.body env
      w.ctx w.typeIdx w.startedState v' haccepted
  have hlookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    rw [List.getElem?_eq_getElem w.type_lt, w.function_type]
  have hft : ft = w.ft := Option.some.inj (hi.symm.trans hlookup)
  subst ft
  have hbody : Profile.BodyEncoding w.body ops :=
    ⟨tokens, next, hc.encoded, hend, hsyntax⟩
  have hstart := hrecords v (.functionStart w.ctx w.typeIdx w.bodyStart finish) (.Ok ())
    w.startedState w.function_start
  refine ⟨⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩ :: bodyObservations,
    ?_, w.typeIdx, w.groups, w.ctx, w.bodyStart, w.body, bodyObservations, tokens, ops, next,
    ⟨w.index_lt, w.index_type⟩,
    Profile.codeEncoding_of_parts w.header w.extent w.locals_bytes w.body_bytes hbody,
    Profile.EntryTyped.of_body hi w.context_locals ht hdeclared,
    w.locals_bound, ?_, w.body_bytes, rfl, accepted, hc, hend, hsyntax,
    w.content, w.size, w.header, w.extent, w.locals_bytes⟩
  · simpa [hstart, List.append_assoc] using hlog
  · exact ⟨w.type_lt, by simpa [w.function_type] using w.context_locals,
      by simpa [w.function_type] using w.context_results⟩

end Itasca.CodeEntry
