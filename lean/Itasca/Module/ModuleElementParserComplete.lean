import Itasca.Module.ModuleElementParser
import Itasca.Module.ModuleElementHeaderComplete
import Itasca.Module.ModuleElementReadersComplete
import Itasca.Module.ModuleEnvRequirements

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements ModuleSections

theorem module.decode_element.complete (data : Slice U8) (env : module.Env)
    (profile : ValidationProfile) (pos next : Usize) (entry : ModuleBinary.Element)
    (hb : At (ElementEncodingFor profile) data pos entry next)
    (hv : ElementValidRaw env entry) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element data pos env profile = .ok (.Ok (actual, next), result) ∧
      ModuleEnv.rawElement actual = entry ∧ ModuleReferences.Added env result (ModuleReferences.element actual) := by
  obtain ⟨bytes, he, hs⟩ := hb
  obtain ⟨expressions, header, encoded, hhead, hvalues, rfl⟩ := header_parts he
  obtain ⟨middle, hheader, hentries⟩ := hs.split
  have hreadheader := module.decode_element_header.complete (env := env)
    ⟨header, hhead, hheader⟩ hv.1
  have hspan := hheader.length
  have hty := hhead.initializer_type
  obtain ⟨result, init, hreadinit, hinit, hadded⟩ := module.decode_element_initializers.complete
    data env entry.elem expressions profile middle next entry.init ⟨encoded, hvalues, hentries⟩
    (by omega) (by simpa only [hty] using hv.2)
    (by intro value hm he; exact hhead.const_allowed value he)
  let actual : module.Element := ⟨entry.elem, entry.mode, init⟩
  refine ⟨result, actual, ?_, ?_, ?_⟩
  · simp [module.decode_element, hreadheader, hreadinit, actual,
      core.result.Result.Insts.CoreOpsTry.branch]
  · cases entry
    simp [ModuleEnv.rawElement, actual, hinit]
  · simpa only [ModuleReferences.element, actual, hinit] using hadded

end Itasca
