import Itasca.Profile.EntryPipeline
import Itasca.Profile.BodyVisitor

/-!
# Profile code-entry soundness

Acceptance by `metadata.validate_code_entry_with` yields the specification `Profile.Entry`
(`metadata.validate_code_entry_with.profile_sound`), for either profile and any visitor.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- An execution witness and a `Profile.Body` fact for its body give `Profile.Entry`. The entry
parser supplies framing and locals, and the body fact supplies the decoded and typed tree. -/
theorem CodeEntry.Witness.profile_validated
    {V : Type} {visitor : code.OpVisitor V} {data env index start finish v v' profile}
    (w : CodeEntry.Witness visitor data env index start finish v v' profile)
    (hbody : Profile.Body profile w.body env w.ctx.locals w.typeIdx) :
    Profile.Entry profile data env index start finish := by
  obtain ⟨ft, ops, hlookup, hsignature, hbytes, htyped, hinstructions, hdeclared⟩ := hbody
  have hlookup' : env.types.val[w.typeIdx.val]? = some w.ft := by
    rw [List.getElem?_eq_getElem w.type_lt, w.function_type]
  have hft : ft = w.ft := Option.some.inj (hlookup.symm.trans hlookup')
  subst ft
  refine ⟨⟨w.groups, ops⟩, Profile.codeEncoding_of_parts w.header w.extent
    w.locals_bytes w.body_bytes hbytes, w.index_lt, ?_, w.locals_bound⟩
  rw [w.index_type]
  exact Profile.EntryTyped.of_body hlookup hsignature w.context_locals htyped hinstructions w.locals_allowed hdeclared

/-- If the entry validator accepts, the entry satisfies `Profile.Entry`. This needs no visitor
totality assumption. -/
theorem metadata.validate_code_entry_with.profile_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (pos : Usize) (env : metadata.Env) (index finish : Usize)
    (v v' : V) (hbound : CodeEntry.Bounds env) (profile : ValidationProfile)
    (hresults : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (h : metadata.validate_code_entry_with visitor data pos env index profile v = .ok (.Ok finish, v')) :
    Profile.Entry profile data env index pos finish := by
  obtain ⟨w⟩ := metadata.validate_code_entry_with.witness_profile visitor data pos env index finish v v'
    hbound profile h
  apply w.profile_validated
  apply code.validate_body_with.profile_sound visitor w.body env w.ctx w.typeIdx profile w.ft w.startedState v'
  · rw [List.getElem?_eq_getElem w.type_lt, w.function_type]
  · apply hresults
    rw [← w.function_type]
    exact List.getElem_mem _
  · exact w.body_accepted

end Itasca
