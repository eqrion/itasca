import Itasca.Profile.EntryComplete
import Itasca.Profile.EntrySound
import Itasca.Module.Code.ReachedEntry

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Forget visitor observations while retaining the independently decoded
source entry. No compiler result occurs in this record. -/
def preparedOfSourceWitness {V : Type} {visitor : code.OpVisitor V} {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile) :
    CodeEntry.Prepared data env index start profile where
  finish := finish
  typeIdx := w.typeIdx
  ft := w.ft
  groups := w.groups
  ctx := w.ctx
  content := w.content
  bodyStart := w.bodyStart
  body := w.body
  size := w.size
  index_lt := w.index_lt
  index_type := w.index_type
  type_lt := w.type_lt
  function_type := w.function_type
  header := w.header
  extent := w.extent
  locals_bytes := w.locals_bytes
  locals_bound := w.locals_bound
  locals_allowed := w.locals_allowed
  context_locals := w.context_locals
  context_results := w.context_results
  body_bytes := w.body_bytes

/-- Independent entry encoding and typing construct prepared source metadata
and body validity, with no compiler visitor or accepted target trace. -/
theorem source_entry_prepared (data : Slice U8) (env : module.Env) (index start finish : Usize)
    (profile : ValidationProfile) (entry : ModuleBinary.Code)
    (indexBound : index.val < env.func_type_indices.val.length)
    (typed : Profile.EntryTyped profile env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env)
    (environment : Profile.Environment profile env) (limits : Profile.EnvironmentWithinLimits env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits profile) data start entry finish) :
    ∃ w : CodeEntry.Prepared data env index start profile,
      w.finish = finish ∧ Profile.Body profile w.body env w.ctx.locals w.typeIdx := by
  obtain ⟨⟨reply,after⟩,called,accepted⟩ := WP.spec_imp_exists
    (module.validate_code_entry_with.complete_spec_of_body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      FullVisitor.empty_accepts data start env index entry finish () profile indexBound typed bounds encoded (by
        intro body ctx typeIdx ft signature results size bodyValid started
        exact code.validate_body_with.profile_complete _ FullVisitor.empty_accepts body env ctx typeIdx profile started
          limits size bodyValid))
  dsimp only at accepted
  subst reply
  obtain ⟨w⟩ := module.validate_code_entry_with.witness_profile code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    data start env index finish () after bounds profile called
  refine ⟨preparedOfSourceWitness w,rfl,?_⟩
  exact code.validate_body_with.profile_sound _ w.body env w.ctx w.typeIdx profile w.ft w.startedState after
    (by simp only [List.getElem?_eq_getElem w.type_lt,w.function_type])
    (environment.1 w.ft (by rw [← w.function_type]; exact List.getElem_mem _)) w.body_accepted

end Itasca.Runtime.Code
