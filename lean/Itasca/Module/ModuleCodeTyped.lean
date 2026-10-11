import Itasca.Module.ModuleLayout
import Itasca.Module.ModuleReadyContexts
import Itasca.Module.ModuleFunctionComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleLayout

open ModuleBinary ModuleElaboration

/-- Generated function typing and the independent Wasm 1.0 profile transport
into the exact decoded environment; no entry-validation premise is used. -/
theorem CodeAt.typed {data start finish raw decls env}
    (h : CodeAt data start raw.codes finish)
    (hr : ModuleEnv.Ready raw 9 decls env)
    (ht : SectionsTyped raw) (hp : Profile raw) :
    List.Forall₂ (CodeEntry.Typed env) env.func_type_indices.val raw.codes := by
  rw [hr.functions_eq (by omega)]
  refine List.forall₂_iff_zip.mpr ⟨ht.functions.length_eq, ?_⟩
  intro idx entry hm
  have hfunc := (List.forall₂_iff_zip.mp ht.functions).2 hm
  have hprofile := (List.forall₂_iff_zip.mp hp.bodies).2 hm
  have hs : Forall BodyContext.SegmentFree entry.body :=
    h.segmentFree (List.of_mem_zip hm).2
  apply CodeEntry.Typed.of_func_ok (hr.moduleContext (by omega)) hs _ hfunc
  simpa [hr.types_eq (by omega)] using hprofile

end Itasca.ModuleLayout
