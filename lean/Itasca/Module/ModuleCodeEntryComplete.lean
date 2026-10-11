import Itasca.Module.ModuleFunctionComplete
import Itasca.Module.ModuleLocalsComplete
import Itasca.Module.ModuleCodeLimits
import Itasca.Module.ModuleCodeEntry
import Itasca.Visitor.VisitorBodyComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem rep_consumed {data start next tokens bytes}
    (he : Rep Wasm.TokenEncoding tokens bytes) (hs : Wasm.BytesAt data start bytes next) :
    Wasm.Consumed data start tokens next := by
  induction he generalizing start with
  | nil =>
    have hn := hs.empty
    subst next
    exact .nil _ hs.bound
  | cons ht hrest ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hs.split
    exact Wasm.Consumed.cons_iff.mpr ⟨middle, ⟨_, ht, hfirst⟩, ih hrest⟩

theorem body_of_bodyEncoding {data : Slice U8} {ops}
    (he : BodyEncoding ops data.val) : Wasm.BodyEncoding data ops := by
  obtain ⟨tokens, ht, hb⟩ := he
  refine ⟨tokens, Slice.len data, rep_consumed ht ?_, rfl, hb⟩
  exact ⟨by simp, by simp, by simp⟩

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary

/-- Successful code-entry validation follows from independent exact bytes,
declarative function typing, the Wasm 1.0 profile, and the explicit byte/local caps. -/
theorem module.validate_code_entry_with.complete_spec {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
    (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (hbytes : At CodeEncodingWithinLimits data pos entry next) :
    module.validate_code_entry_with visitor data pos env index v ⦃ r => r.1 = .Ok next ⦄ := by
  obtain ⟨bytes, he, hspan⟩ := hbytes
  obtain ⟨hcap, sizeBytes, localBytes, bodyBytes, hsize, hlocals, hbody, hbodyCap, rfl⟩ := he
  obtain ⟨bodyStart, hprefix, hbodySpan⟩ := hspan.split
  obtain ⟨content, hhead, hlocalsSpan⟩ := hprefix.split
  let size : U32 := U32.ofNatCore (localBytes.length + bodyBytes.length) (by have := hsize.value_lt; scalar_tac)
  have hsizeval : size.val = localBytes.length + bodyBytes.length := by simp [size]
  have hread := hhead.read_u32 size (by simpa [hsizeval] using hsize)
  have hend : next.val = content.val + size.val := by
    have := hlocalsSpan.length
    have := hbodySpan.length
    omega
  obtain ⟨declared, hdeclared, hdeclaredVal⟩ := module.decode_locals.complete data content entry.locals bodyStart
    ⟨localBytes, hlocals, hlocalsSpan⟩ hcap
  have hindex : ¬ index ≥ alloc.vec.Vec.len env.func_type_indices := by scalar_tac
  unfold module.validate_code_entry_with
  simp [hindex, hread, core.result.Result.Insts.CoreOpsTry.branch]
  step
  obtain ⟨hr, hhave, hhavePost⟩ := WP.spec_imp_exists
    (module.have_bytes.spec data content n (by have := hhead.bound; omega))
  have hgood : hr = .Ok () := hhavePost.1.mpr (by have := hspan.bound; scalar_tac)
  rw [hgood] at hhave
  simp [hhave]
  step
  have hendEq : «end» = next := by scalar_tac
  simp [hdeclared]
  have hbodyStart : ¬ «end».val < bodyStart.val := by have := hbodySpan.length; scalar_tac
  simp only [hbodyStart, ↓reduceIte]
  step
  have ht : CodeEntry.Typed env type_idx entry := by simpa [type_idx_post] using htyped
  step
  have htype : ¬ env.types.val.length ≤ t.val := by have := ht.type_lt; scalar_tac
  simp only [htype, ↓reduceIte]
  step
  have hti := ht.type_lt
  have hft : env.types.val[type_idx.val] = ft := by simpa [t_post] using ft_post.symm
  have hmem : ft ∈ env.types.val := by rw [← hft]; exact List.getElem_mem _
  have hroom : ft.params.val.length + declared.val.length ≤ Usize.max := by
    have := hbound ft hmem
    rw [hdeclaredVal]
    have hc : (ModuleLocals.declared entry.locals).length ≤ limits.MAX_LOCALS.val := hcap
    omega
  obtain ⟨locals, hbuild, hbuildVal⟩ := WP.spec_imp_exists
    (module.build_func_locals.spec (alloc.vec.Vec.deref ft.params) (alloc.vec.Vec.deref declared)
      (by simpa [alloc.vec.Vec.deref] using hroom))
  obtain ⟨results, hcopy, hcopyVal⟩ := WP.spec_imp_exists
    (module.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
  rw [hbuild]
  simp only [bind_ok]
  rw [hcopy]
  simp only [bind_ok]
  obtain ⟨started, hstart⟩ := haccept.on_function_start v ⟨locals, results⟩ type_idx bodyStart «end»
  rw [hstart]
  simp only [bind_ok]
  step
  have hactual := ModuleBinary.slice_bytes (by have := hbodySpan.length; scalar_tac)
    (by rw [hendEq]; exact hbodySpan.bound) r_post
  have hslice : r.val = bodyBytes := by
    rw [hendEq] at hactual
    exact List.append_cancel_right (hactual.suffix.symm.trans hbodySpan.suffix)
  obtain ⟨bt, hbt⟩ := CodeEntry.blockType_of_length ft.results.val (henv.types ft hmem)
  have hctxlocals : (⟨locals, results⟩ : code.Context).locals.val = ft.params.val ++ entry.declared := by
    simpa [alloc.vec.Vec.deref, hdeclaredVal, ModuleBinary.Code.declared, ModuleLocals.declared] using hbuildVal
  have hctxresults : (⟨locals, results⟩ : code.Context).results.val = ft.results.val := by
    simpa [alloc.vec.Vec.deref] using hcopyVal
  have htypedBody : Wasm.FunctionTyped env ⟨locals, results⟩ bt entry.body := by
    have h := ht.typed
    rw [hft] at h
    unfold Wasm.FunctionTyped
    rw [CodeEntry.body_context hctxlocals hctxresults hbt]
    simpa [CodeEntry.instructionType, Control.resultTypes, ← hbt] using h
  have hprofile : Wasm1.Instructions
      (WasmFrames.enter (EnvTranslation.context env ⟨locals, results⟩) .body bt) entry.body := by
    rw [CodeEntry.body_context hctxlocals hctxresults hbt]
    simpa [hft] using ht.profile
  obtain ⟨finished, hfinished⟩ := code.validate_body_with.wasm_complete visitor haccept r env
    ⟨locals, results⟩ bt henv (hctxresults.trans hbt)
    (by simpa [Slice.length, hslice] using hbodyCap)
    ⟨entry.body, body_of_bodyEncoding (by simpa [hslice] using hbody), htypedBody, hprofile⟩ started
  rw [hfinished]
  simp [hendEq]


theorem module.validate_code_entry_with.complete {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
    (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (hbytes : At CodeEncodingWithinLimits data pos entry next) :
    ∃ v', module.validate_code_entry_with visitor data pos env index v = .ok (.Ok next, v') := by
  obtain ⟨⟨r, v'⟩, hr, hok⟩ := WP.spec_imp_exists
    (module.validate_code_entry_with.complete_spec visitor haccept data pos env index entry next v
      hi htyped henv hbound hbytes)
  dsimp only at hok
  exact ⟨v', by simpa only [hok] using hr⟩

theorem module.validate_code_entry.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (entry : Code) (next : Usize)
    (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (hbytes : At CodeEncodingWithinLimits data pos entry next) :
    module.validate_code_entry data pos env index = .ok (.Ok next) := by
  obtain ⟨w, hr⟩ := module.validate_code_entry_with.complete
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data pos env index entry next ()
    hi htyped henv hbound hbytes
  simp [module.validate_code_entry, hr]

end Itasca
