import Itasca.Profile.EntryPipeline
import Itasca.Profile.BodyVisitor
import Itasca.Module.Code.LocalsComplete

/-!
# Profile code-entry completeness

Completeness of `metadata.validate_code_entry_with`: a code entry that meets the independent
specification (`Profile.EntryTyped`, `CodeEncodingWithinLimits`) is accepted.
`complete_spec_of_body` takes a body completeness hypothesis, and `profile_complete_spec` and
`profile_complete` discharge it for both profiles.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- Code-entry validation succeeds with end offset `next` when the entry has exact bytes, is typed
for the profile, and meets the byte and local limits, given a completeness hypothesis for the body
step. -/
theorem metadata.validate_code_entry_with.complete_spec_of_body {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
    (profile : ValidationProfile)
    (hi : index.val < env.func_type_indices.val.length)
    (htyped : Profile.EntryTyped profile env env.func_type_indices.val[index.val] entry)
    (hbound : CodeEntry.Bounds env)
    (hbytes : At (Profile.CodeEncodingWithinLimits profile) data pos entry next)
    (hcomplete : ∀ body ctx typeIdx ft,
      env.types.val[typeIdx.val]? = some ft → ctx.results.val = ft.results.val →
      body.length ≤ limits.MAX_FUNCTION_BYTES.val → Profile.Body profile body env ctx.locals typeIdx →
      ∀ started, ∃ ended,
        code.validate_body_with visitor body env ctx typeIdx profile started = .ok (.Ok (), ended)) :
    metadata.validate_code_entry_with visitor data pos env index profile v ⦃ r => r.1 = .Ok next ⦄ := by
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
  obtain ⟨declared, hdeclared, hdeclaredVal⟩ := metadata.decode_locals.complete data content profile entry.locals bodyStart
    ⟨localBytes, hlocals, hlocalsSpan⟩ htyped.locals_allowed hcap
  have hindex : ¬ index ≥ alloc.vec.Vec.len env.func_type_indices := by scalar_tac
  unfold metadata.validate_code_entry_with
  simp [hindex, hread, core.result.Result.Insts.CoreOpsTry.branch]
  step
  obtain ⟨hr, hhave, hhavePost⟩ := WP.spec_imp_exists
    (metadata.have_bytes.spec data content n (by have := hhead.bound; omega))
  have hgood : hr = .Ok () := hhavePost.1.mpr (by have := hspan.bound; scalar_tac)
  rw [hgood] at hhave
  simp [hhave]
  step
  have hendEq : «end» = next := by scalar_tac
  simp [hdeclared]
  have hbodyStart : ¬ «end».val < bodyStart.val := by have := hbodySpan.length; scalar_tac
  simp only [hbodyStart, ↓reduceIte]
  step
  have ht : Profile.EntryTyped profile env type_idx entry := by simpa [type_idx_post] using htyped
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
    (metadata.build_func_locals.spec (alloc.vec.Vec.deref ft.params) (alloc.vec.Vec.deref declared)
      (by simpa [alloc.vec.Vec.deref] using hroom))
  obtain ⟨results, hcopy, hcopyVal⟩ := WP.spec_imp_exists
    (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
  rw [hbuild]
  simp only [bind_ok]
  rw [hcopy]
  simp only [bind_ok]
  obtain ⟨started, hstart⟩ := haccept.on_function_start v ⟨locals, results⟩ type_idx bodyStart «end»
  rw [hstart]
  simp only [bind_ok]
  step as ⟨r, r_post⟩
  have hactual := ModuleBinary.slice_bytes (by have := hbodySpan.length; scalar_tac)
    (by rw [hendEq]; exact hbodySpan.bound) r_post
  have hslice : r.val = bodyBytes := by
    rw [hendEq] at hactual
    exact List.append_cancel_right (hactual.suffix.symm.trans hbodySpan.suffix)
  have hctxlocals : (⟨locals, results⟩ : code.Context).locals.val =
      env.types.val[type_idx.val].params.val ++ entry.declared := by
    rw [hft]
    simpa [alloc.vec.Vec.deref, hdeclaredVal, ModuleBinary.Code.declared, ModuleLocals.declared] using hbuildVal
  have hctxresults : (⟨locals, results⟩ : code.Context).results.val = ft.results.val := by
    simpa [alloc.vec.Vec.deref] using hcopyVal
  have hlookup : env.types.val[type_idx.val]? = some ft := by simp [List.getElem?_eq_getElem hti, hft]
  have hencoding := Profile.BodyBytes.body (data := r) (by simpa [hslice] using hbody)
  have hcert := ht.body r locals hctxlocals hencoding
  obtain ⟨finished, hfinished⟩ := hcomplete r ⟨locals, results⟩ type_idx ft hlookup hctxresults
    (by simpa [Slice.length, hslice] using hbodyCap) hcert started
  rw [hfinished]
  simp [hendEq]

/-- Entry validation succeeds, as a weakest-precondition statement, for either profile under the
profile's environment and size bounds. -/
theorem metadata.validate_code_entry_with.profile_complete_spec {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
    (profile : ValidationProfile) (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry profile)
    (henv : Profile.Environment profile env) (hlimits : Profile.EnvironmentWithinLimits env)
    (hbound : CodeEntry.Bounds env)
    (hbytes : At (Profile.CodeEncodingWithinLimits profile) data pos entry next) :
    metadata.validate_code_entry_with visitor data pos env index profile v ⦃ r => r.1 = .Ok next ⦄ := by
  apply metadata.validate_code_entry_with.complete_spec_of_body visitor haccept data pos env index entry next v
    profile hi (Profile.EntryTyped.of_core htyped (henv.1 _ (List.getElem_mem _))) hbound hbytes
  intro body ctx typeIdx ft hlookup hresults hsize hcert started
  exact code.validate_body_with.profile_complete visitor haccept body env ctx typeIdx profile started
    hlimits hsize hcert

/-- Entry validation returns `.Ok next` for either profile under the profile's environment and size
bounds. -/
theorem metadata.validate_code_entry_with.profile_complete {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
    (profile : ValidationProfile) (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry profile)
    (henv : Profile.Environment profile env) (hlimits : Profile.EnvironmentWithinLimits env)
    (hbound : CodeEntry.Bounds env)
    (hbytes : At (Profile.CodeEncodingWithinLimits profile) data pos entry next) :
    ∃ v', metadata.validate_code_entry_with visitor data pos env index profile v = .ok (.Ok next, v') := by
  obtain ⟨⟨r, v'⟩, hr, hok⟩ := WP.spec_imp_exists
    (metadata.validate_code_entry_with.profile_complete_spec visitor haccept data pos env index entry next v
      profile hi htyped henv hlimits hbound hbytes)
  dsimp only at hok
  exact ⟨v', by simpa only [hok] using hr⟩

end Itasca
