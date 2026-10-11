import Itasca.Module.ModuleElementHeader
import Itasca.Module.ModuleReadersComplete

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements

@[step]
theorem module.decode_element.spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (profile : ValidationProfile)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    module.decode_element data pos env profile ⦃ r => match r.1 with
      | .Ok (entry, next) =>
          At (ElementEncodingFor profile) data pos ⟨entry.elem, entry.mode, entry.init.val⟩ next ∧
          ModuleReferences.Added env r.2 (ModuleReferences.element entry) ∧
          ModuleSegments.elementValid env entry ∧
          r.2.declared_funcs.val.length ≤ next.val ∧ pos.val < next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_element_header.spec data pos env profile)
  cases r with
  | Err e => simp [module.decode_element, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok tuple =>
    obtain ⟨mode, elem, expressions, middle⟩ := tuple
    obtain ⟨hheader, hvalid⟩ := hp
    have hspan := hheader.span
    obtain ⟨⟨r, result⟩, hinit, hp⟩ := WP.spec_imp_exists
      (module.decode_element_initializers.spec data middle env elem expressions profile (by omega))
    cases r with
    | Err e => simp [module.decode_element, hr, hinit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨init, next⟩ := pair
      obtain ⟨hib, hadded, hiv, hbound⟩ := hp
      simp [module.decode_element, hr, hinit, core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨fb, hf, hfs⟩ := hheader
      have hty := hf.initializer_type
      have hprogress : middle.val < next.val := by
        obtain ⟨count, content, hn, hc, hi⟩ := hib.vector_split
        have := hc.span
        have := hi.span
        omega
      obtain ⟨ib, hi, his⟩ := hib
      exact ⟨⟨fb ++ ib, hf.append hi, hfs.append his⟩, hadded,
        ⟨hvalid, (by simpa only [hty] using hiv)⟩, hbound, by omega⟩

end Itasca
