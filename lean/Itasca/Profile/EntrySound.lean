import Itasca.Profile.EntryPipeline
import Itasca.Profile.BodyVisitor

open Aeneas Aeneas.Std

namespace Itasca

/-- The entry parser contributes framing and locals; the body contract
contributes the same independently decoded and typed instruction tree. -/
theorem CodeEntry.Witness.profile_validated
    {V : Type} {visitor : code.OpVisitor V} {data env index start finish v v' profile}
    (w : CodeEntry.Witness visitor data env index start finish v v' profile)
    (hbody : Profile.Body profile w.body env w.ctx.locals w.typeIdx) :
    Profile.Entry profile data env index start finish := by
  obtain ⟨ft, ops, hlookup, hsignature, hbytes, htyped, hinstructions⟩ := hbody
  have hlookup' : env.types.val[w.typeIdx.val]? = some w.ft := by
    rw [List.getElem?_eq_getElem w.type_lt, w.function_type]
  have hft : ft = w.ft := Option.some.inj (hlookup.symm.trans hlookup')
  subst ft
  refine ⟨⟨w.groups, ops⟩, Profile.codeEncoding_of_parts w.header w.extent
    w.locals_bytes w.body_bytes hbytes, w.index_lt, ?_, w.locals_bound⟩
  rw [w.index_type]
  exact Profile.EntryTyped.of_body hlookup hsignature w.context_locals htyped hinstructions

/-- Actual visiting acceptance yields an independent entry certificate for
the selected profile, without a visitor totality assumption. -/
theorem module.validate_code_entry_with.profile_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (pos : Usize) (env : module.Env) (index finish : Usize)
    (v v' : V) (hbound : CodeEntry.Bounds env) (profile : ValidationProfile)
    (hresults : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (h : module.validate_code_entry_with visitor data pos env index profile v = .ok (.Ok finish, v')) :
    Profile.Entry profile data env index pos finish := by
  obtain ⟨w⟩ := module.validate_code_entry_with.witness_profile visitor data pos env index finish v v'
    hbound profile h
  apply w.profile_validated
  apply CodeEntry.runBody.sound visitor profile w.body env w.ctx w.typeIdx w.ft w.startedState v'
  · rw [List.getElem?_eq_getElem w.type_lt, w.function_type]
  · exact w.context_results
  · apply hresults
    rw [← w.function_type]
    exact List.getElem_mem _
  · exact w.body_accepted

end Itasca
