import Itasca.Profile.EntryComplete
import Itasca.Profile.EntrySound
import Itasca.Module.Code.ReachedEntry

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Forget visitor observations while retaining the independently decoded
source entry. No compiler result occurs in this record. -/
def preparedOfSourceWitness {V : Type} {visitor : code.OpVisitor V} {data env index start finish before after}
    (w : CodeEntry.Witness visitor data env index start finish before after) :
    CodeEntry.Prepared data env index start where
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
  context_locals := w.context_locals
  context_results := w.context_results
  body_bytes := w.body_bytes

/-- Independent entry encoding and typing construct prepared source metadata
and body validity, with no compiler visitor or accepted target trace. -/
theorem source_entry_prepared (data : Slice U8) (env : metadata.Env) (index start finish : Usize)
     (entry : ModuleBinary.Code)
    (indexBound : index.val < env.func_type_indices.val.length)
    (typed : Profile.EntryTyped env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env)
    (limits : Profile.EnvironmentWithinLimits env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits) data start entry finish) :
    ∃ w : CodeEntry.Prepared data env index start,
      w.finish = finish ∧ Wasm2.Validated w.body env w.ctx.locals w.typeIdx := by
  obtain ⟨⟨reply,after⟩,called,accepted⟩ := WP.spec_imp_exists
    (metadata.validate_code_entry_with.complete_spec_of_body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      FullVisitor.empty_accepts data start env index entry finish () indexBound typed bounds encoded (by
        intro body ctx typeIdx ft signature results size bodyValid started
        exact code.validate_body_with.profile_complete _ FullVisitor.empty_accepts body env ctx typeIdx started
          limits size bodyValid))
  dsimp only at accepted
  subst reply
  obtain ⟨w⟩ := metadata.validate_code_entry_with.witness_profile code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    data start env index finish () after bounds called
  refine ⟨preparedOfSourceWitness w,rfl,?_⟩
  exact code.validate_body_with.profile_sound _ w.body env w.ctx w.typeIdx w.startedState after
    w.body_accepted

end Itasca.Runtime.Compiler
