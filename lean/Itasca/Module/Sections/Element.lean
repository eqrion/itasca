import Itasca.Module.Sections.ElementHeader
import Itasca.Module.Elab.SegmentSyntax
import Itasca.Module.Sections.Imports
import Itasca.Module.Sections.Global
import Itasca.Module.Readers.SegmentIndex

/-!
# Element section parser

Soundness of `metadata.decode_element_section`, its loop and `metadata.decode_func_indices`.
`ElementsAdded` says the environment gains the decoded elements and their function references. The
span is a `VecEncoding (ElementEncodingFor profile)` and every element is `ElementValid`. The
`element_encoded` lemmas build element encodings from their parts. Completeness is in
`Module/Sections/ElementComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

end Itasca

namespace Itasca.ModuleSections

/-- `result` is `env` with the elements `added` appended and their function references appended to
the declared functions. Nothing else changes. -/
def ElementsAdded (env result : metadata.Env) (added : List metadata.Element) : Prop :=
  result = { env with elements := result.elements, declared_funcs := result.declared_funcs } ∧
  result.elements.val = env.elements.val ++ added ∧
  result.declared_funcs.val = env.declared_funcs.val ++ added.flatMap ModuleReferences.element

/-- An element is valid in the environment: its table, offset and initializers are valid. -/
abbrev ElementValid := ModuleSegments.elementValid

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

private theorem element_valid_caches {env result entry}
    (h : ElementValid result entry)
    (hf : env.func_types = result.func_types) (hg : env.global_types = result.global_types)
    (hn : env.num_imported_globals = result.num_imported_globals)
    (ht : env.table_types = result.table_types) : ElementValid env entry := by
  obtain ⟨hm, hi⟩ := h
  constructor
  · cases hmode : entry.mode with
    | Passive | Declarative => trivial
    | Active index offset =>
      rw [hmode] at hm
      obtain ⟨hb, he, hv⟩ := hm
      exact ⟨by simpa [ht] using hb, by simpa [ht] using he, hv.same_caches hf hg hn⟩
  · intro value hv
    exact (hi value hv).same_caches hf hg hn

/-- The element loop adds `count` elements forming a `Rep` span, each `ElementValid`. -/
@[step]
theorem metadata.decode_element_section_loop.profile_spec (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.elements.val.length ≤ start.val) (hrefs : env.declared_funcs.val.length ≤ start.val) :
    metadata.decode_element_section_loop data env profile count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ ElementsAdded env r.2 added ∧
          At (Rep (ElementEncodingFor profile)) data start (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_element_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      ElementsAdded env s.1 added ∧
      At (Rep (ElementEncodingFor profile)) data start (added.map ModuleEnv.rawElement) s.2.1 ∧
      (∀ entry ∈ added, ElementValid env entry) ∧ s.1.elements.val.length ≤ s.2.1.val ∧
      s.1.declared_funcs.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize, hrefs⟩
    dsimp only at hi hlen henv hbytes hvalid hsize hrefs
    unfold metadata.decode_element_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize, hrefs⟩
    · rename_i hmore
      obtain ⟨⟨r, updated⟩, hr, hp⟩ := WP.spec_imp_exists
        (metadata.decode_element.spec data pos current profile hrefs)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨entry, next⟩ := pair
        obtain ⟨hb, hadded, hv, hbound, hprogress⟩ := hp
        dsimp only at hadded hbound
        have hspan := hb.span
        have hunchanged : updated.elements = current.elements := by rw [hadded.1]
        have hcapacity : updated.elements.val.length < Usize.max := by
          rw [hunchanged]
          scalar_tac
        have hentry : ElementValid env entry := by
          apply element_valid_caches hv <;> rw [henv.1]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨elements, helements⟩
        step
        refine ⟨?_, ⟨added ++ [entry], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · scalar_tac
        · simp only [List.length_append, List.length_singleton]; scalar_tac
        · refine ⟨?_, ?_, ?_⟩
          · rw [hadded.1, henv.1]
          · simp only [helements, hunchanged, henv.2.1, List.append_assoc]
          · simp only [hadded.2, henv.2.2, List.flatMap_append, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, List.append_assoc]
        · simpa only [List.map_append, List.map_cons, List.map_nil, ModuleEnv.rawElement]
            using hbytes.snoc hb
        · intro value hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hvalid value hm
          · simpa [List.mem_singleton.mp hm] using hentry
        · simp only [helements, hunchanged, List.length_append, List.length_singleton]
          omega
        · exact hbound
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp, by simp⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hsize, hrefs⟩

/-- `metadata.decode_element_section` adds the elements of a `VecEncoding` span, each
`ElementValid`. -/
@[step]
theorem metadata.decode_element_section.profile_spec (data : Slice U8) (pos : Usize) (env : metadata.Env) (profile : ValidationProfile)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    metadata.decode_element_section data pos env profile ⦃ r => match r.1 with
      | .Ok next => ∃ added, ElementsAdded env r.2 added ∧
          At (VecEncoding (ElementEncodingFor profile)) data pos (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_element_section_loop.profile_spec data env profile count start hs.2.2 (by omega) (by omega))
    simp [metadata.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize, hrefs⟩ := hp
      exact ⟨added, henv, At.vector hc hb (by simpa using hlen), ht, hsize, hrefs⟩

end Itasca
