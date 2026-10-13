import Itasca.Module.Code.EntryWitness
import Itasca.Wasm1.Trace.Body

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

open VisitorTrace

/-- Independent accepted-entry provenance. The exact code bytes, generated
typing and recorded operator stream use the same instruction tree. The start
event uses module offsets; operator states use the sliced body's offsets. -/
def AcceptedTrace (data : Slice U8) (env : module.Env) (index start finish : Usize)
    (observations : List Observation) : Prop :=
  ∃ (typeIdx : U32) (groups : List (U32 × types.ValueType)) (ctx : code.Context)
      (bt : code.BlockType) (bodyStart : Usize) (body : Slice U8)
      (bodyObservations : List Observation) (tokens : List Wasm1.Token)
      (ops : List instr) (next : Usize),
    (∃ hi : index.val < env.func_type_indices.val.length,
      env.func_type_indices.val[index.val] = typeIdx) ∧
    ModuleBinary.At ModuleBinary.CodeEncoding data start ⟨groups, ops⟩ finish ∧
    Typed env typeIdx ⟨groups, ops⟩ ∧
    (ModuleLocals.declared groups).length ≤ limits.MAX_LOCALS.val ∧
    (∃ ht : typeIdx.val < env.types.val.length,
      ctx.locals.val = env.types.val[typeIdx.val].params.val ++ ModuleLocals.declared groups ∧
      ctx.results.val = env.types.val[typeIdx.val].results.val) ∧
    ctx.results.val = Control.results bt ∧
    Wasm1.BytesAt data bodyStart body.val finish ∧
    observations = ⟨.functionStart ctx typeIdx bodyStart finish, .Ok ()⟩ :: bodyObservations ∧
    AllAccepted bodyObservations ∧
    Completed body 0#usize bodyObservations tokens next ∧ next.val = body.length ∧
    Wasm1.BodyTokens tokens ops ∧ Wasm1.FunctionTyped env ctx bt ops ∧
    (∃ (content : Usize) (size : U32),
      Leb128.Decoded data start size content ∧
      finish.val = content.val + size.val ∧
      ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding)
        data content groups bodyStart)

theorem AcceptedTrace.validated {data env index start finish observations}
    (h : AcceptedTrace data env index start finish observations) :
    Validated data env index start finish := by
  obtain ⟨typeIdx, groups, ctx, bt, bodyStart, body, bodyObservations, tokens, ops, next,
    ⟨hi, he⟩, hbytes, htyped, hbound, _⟩ := h
  exact ⟨⟨groups, ops⟩, hbytes, hi, he ▸ htyped, hbound⟩

theorem AcceptedTrace.all_accepted {data env index start finish observations}
    (h : AcceptedTrace data env index start finish observations) : AllAccepted observations := by
  obtain ⟨_, _, _, _, _, _, bodyObservations, _, _, _, _, _, _, _, _, _, _, rfl, ha, _⟩ := h
  intro observation hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rfl
  · exact ha _ hm

/-- Retain the original function-start event and align the original body log
with the exact same syntax used for the code-entry typing certificate. -/
theorem Witness.trace_sound {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish v v'}
    (w : Witness visitor data env index start finish v v')
    (observe : V → List Observation) (hrecords : Records visitor observe)
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) :
    ∃ observations, observe v' = observe v ++ observations ∧
      AcceptedTrace data env index start finish observations := by
  have hftmem : w.ft ∈ env.types.val := by
    rw [← w.function_type]
    exact List.getElem_mem _
  obtain ⟨bt, hbt⟩ := blockType_of_length w.ft.results.val (hresults _ hftmem)
  have hr : w.ctx.results.val = Control.results bt := w.context_results.trans hbt
  obtain ⟨bodyObservations, hlog, htrace⟩ := code.validate_body_with.trace visitor observe
    hrecords w.body env w.ctx w.startedState v' (.Ok ()) w.body_accepted
  obtain ⟨ha, tokens, next, hc, hend⟩ := htrace.accepted
  obtain ⟨ops, hb, ht, hp⟩ := code.validate_body_with.wasm1_sound visitor
    w.body env w.ctx bt hr w.startedState v' w.body_accepted
  have hdeclared := hb.declared (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val))
  have hcode := ModuleBinary.codeEncoding_of_parts w.header w.extent w.locals_bytes w.body_bytes hb
  obtain ⟨tokens', next', hb, hend', hsyntax⟩ := hb
  have he : next' = next := UScalar.eq_of_val_eq (hend'.trans hend.symm)
  subst next'
  have he := hc.encoded.unique hb
  subst tokens'
  have hstart := hrecords v (.functionStart w.ctx w.typeIdx w.bodyStart finish) (.Ok ())
    w.startedState w.function_start
  refine ⟨⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩ :: bodyObservations,
    ?_, w.typeIdx, w.groups, w.ctx, bt, w.bodyStart, w.body, bodyObservations, tokens, ops, next,
    ⟨w.index_lt, w.index_type⟩, hcode, ?_, w.locals_bound, ?_, hr, w.body_bytes,
    rfl, ha, hc, hend, hsyntax, ht,
    w.content, w.size, w.header, w.extent, w.locals_bytes⟩
  · simpa [hstart, List.append_assoc] using hlog
  · refine ⟨w.type_lt, ?_, ?_, w.locals_allowed, ?_⟩
    · rw [w.function_type]
      unfold Wasm1.FunctionTyped at ht
      rw [body_context w.context_locals w.context_results hbt] at ht
      simpa only [instructionType, Control.resultTypes, ← hbt, ModuleBinary.Code.declared,
        ModuleLocals.declared] using ht
    · rw [w.function_type]
      rw [body_context w.context_locals w.context_results hbt] at hp
      exact hp
    · exact hdeclared
  · exact ⟨w.type_lt, by simpa [w.function_type] using w.context_locals,
      by simpa [w.function_type] using w.context_results⟩

end Itasca.CodeEntry

namespace Itasca

/-- Every accepted recording consumer receives a function-start event followed
by exactly the independently encoded, typed operators of that same entry.
There is no termination or acceptance hypothesis on other callback runs. -/
theorem module.validate_code_entry_with.trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List VisitorTrace.Observation) (hrecords : VisitorTrace.Records visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (index finish : Usize)
    (v v' : V) (hbound : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1)
    (h : module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok finish, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CodeEntry.AcceptedTrace data env index pos finish observations := by
  obtain ⟨w⟩ := module.validate_code_entry_with.witness visitor data pos env index finish v v' hbound h
  exact w.trace_sound observe hrecords hresults

end Itasca
