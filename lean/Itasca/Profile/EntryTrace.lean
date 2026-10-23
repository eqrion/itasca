import Itasca.Profile.EntrySound
import Itasca.Wasm2.Trace.Correspondence

/-!
# Code entry traces

`CodeEntry.AcceptedTrace` ties an entry's independent code encoding, its generated typing and the
operator stream a recording visitor observed to one instruction tree. `Witness.trace_sound` builds
it from a `Witness`. `Itasca/Results/Trace` states it for a successful call of
`module.validate_code_entry_with`.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

open VisitorTrace

/-- The observations of an accepted entry come from a function-start event followed by body
operator events. The code bytes, generated typing and recorded operators share one instruction
tree. The start event uses module offsets, and operator states use offsets of the sliced body. For
Wasm 1.0 the recorded tokens also follow the Wasm 1.0 grammar. -/
def AcceptedTrace (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (index start finish : Usize) (observations : List Observation) : Prop :=
  ∃ (typeIdx : U32) (groups : List (U32 × types.ValueType)) (ctx : code.Context)
      (bodyStart : Usize) (body : Slice U8) (bodyObservations : List Observation)
      (tokens : List Wasm2.Token) (ops : List instr) (next : Usize),
    (∃ hi : index.val < env.func_type_indices.val.length,
      env.func_type_indices.val[index.val] = typeIdx) ∧
    ModuleBinary.At (Profile.CodeEncoding profile) data start ⟨groups, ops⟩ finish ∧
    Profile.EntryTyped profile env typeIdx ⟨groups, ops⟩ ∧
    (ModuleLocals.declared groups).length ≤ limits.MAX_LOCALS.val ∧
    (∃ ht : typeIdx.val < env.types.val.length,
      ctx.locals.val = env.types.val[typeIdx.val].params.val ++ ModuleLocals.declared groups ∧
      ctx.results.val = env.types.val[typeIdx.val].results.val) ∧
    Wasm1.BytesAt data bodyStart body.val finish ∧
    observations = ⟨.functionStart ctx typeIdx bodyStart finish, .Ok ()⟩ :: bodyObservations ∧
    AllAccepted bodyObservations ∧
    Wasm2.CallbackTrace.Completed body 0#usize bodyObservations tokens next ∧
    next.val = body.length ∧ Wasm2.BodyTokens tokens ops ∧
    (profile = .Wasm1 → Wasm1.Consumed body 0#usize tokens next) ∧
    (∃ (content : Usize) (size : U32),
      Leb128.Decoded data start size content ∧
      finish.val = content.val + size.val ∧
      ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding)
        data content groups bodyStart)

/-- A `Witness` gives an `AcceptedTrace` of the observations the recording visitor added. The
function-start event and the body log align with the syntax used for the code entry typing
certificate. -/
theorem Witness.trace_sound {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish v v' profile}
    (w : Witness visitor data env index start finish v v' profile)
    (observe : V → List Observation) (hrecords : Records visitor observe)
    (hresults : ∀ ft ∈ env.types.val, Profile.FuncType profile ft) :
    ∃ observations, observe v' = observe v ++ observations ∧
      AcceptedTrace profile data env index start finish observations := by
  have hftmem : w.ft ∈ env.types.val := by
    rw [← w.function_type]
    exact List.getElem_mem _
  have haccepted := w.body_accepted
  obtain ⟨bodyObservations, hlog, accepted, ft, tokens, ops, next, hi, hc, hend, hsyntax, ht,
    hdeclared, hwasm1⟩ := Wasm2.CallbackTrace.body_trace_sound visitor observe hrecords w.body env
      w.ctx w.typeIdx profile w.startedState v' haccepted
  have hlookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    rw [List.getElem?_eq_getElem w.type_lt, w.function_type]
  have hft : ft = w.ft := Option.some.inj (hi.symm.trans hlookup)
  subst ft
  have hbody : Profile.BodyEncoding profile w.body ops := by
    cases profile with
    | Wasm1 => exact ⟨tokens, next, (hwasm1 rfl).1, hend, hsyntax⟩
    | Wasm2 => exact ⟨tokens, next, hc.encoded, hend, hsyntax⟩
  have hinstructions : Profile.Instructions profile (Wasm2.functionContext env w.ctx.locals w.ft) ops := by
    cases profile with
    | Wasm1 => exact (hwasm1 rfl).2
    | Wasm2 => trivial
  have hstart := hrecords v (.functionStart w.ctx w.typeIdx w.bodyStart finish) (.Ok ())
    w.startedState w.function_start
  refine ⟨⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩ :: bodyObservations,
    ?_, w.typeIdx, w.groups, w.ctx, w.bodyStart, w.body, bodyObservations, tokens, ops, next,
    ⟨w.index_lt, w.index_type⟩,
    Profile.codeEncoding_of_parts w.header w.extent w.locals_bytes w.body_bytes hbody,
    Profile.EntryTyped.of_body hi (hresults _ hftmem) w.context_locals ht hinstructions
      w.locals_allowed hdeclared,
    w.locals_bound, ?_, w.body_bytes, rfl, accepted, hc, hend, hsyntax,
    fun hp => (hwasm1 hp).1, w.content, w.size, w.header, w.extent, w.locals_bytes⟩
  · simpa [hstart, List.append_assoc] using hlog
  · exact ⟨w.type_lt, by simpa [w.function_type] using w.context_locals,
      by simpa [w.function_type] using w.context_results⟩

end Itasca.CodeEntry
