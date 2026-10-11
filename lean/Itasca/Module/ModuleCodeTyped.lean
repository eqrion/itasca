import Itasca.Module.ModuleLayout
import Itasca.Module.ModuleReadyContexts
import Itasca.Module.ModuleFunctionComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleLayout

open ModuleBinary ModuleElaboration

/-- Generated function typing and the selected independent profile transport
into the exact decoded environment; no entry-validation premise is used. -/
theorem CodeAt.typed {profile data start finish raw decls env}
    (h : CodeAt data start raw.codes finish profile)
    (hr : ModuleEnv.Ready raw 10 decls env)
    (ht : SectionsTyped raw) (hp : Profile raw profile)
    (hallowed : ModuleTypesAllowed profile raw) (hdata : DataCountValid raw)
    (hdeclared : ∀ entry ∈ raw.codes, DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body) :
    List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) env.func_type_indices.val raw.codes := by
  rw [hr.functions_eq (by omega)]
  refine List.forall₂_iff_zip.mpr ⟨ht.functions.length_eq, ?_⟩
  intro idx entry hm
  have hfunc := (List.forall₂_iff_zip.mp ht.functions).2 hm
  have hprofile := (List.forall₂_iff_zip.mp hp.bodies).2 hm
  have hentry : entry ∈ raw.codes := (List.of_mem_zip hm).2
  apply CodeEntry.Typed.of_func_ok (hr.moduleContext (by omega))
    (hr.elements_context (by omega)) (hr.data_context (by omega) hdata entry hentry) _ hfunc
    (hallowed.2.2.2.2.1 entry hentry) (hdeclared entry hentry)
  simpa [hr.types_eq (by omega)] using hprofile

end Itasca.ModuleLayout
