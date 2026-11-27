import Itasca.Module.Sections.Imports
import Itasca.Module.Sections.Globals
import Itasca.Module.Sections.Exports
import Itasca.Module.Sections.Descriptors
import Itasca.Module.Sections.Tail
import Itasca.Module.Env.Declarations

/-! Prefix and tail section contracts, including the element section's paired
module payload and code-metadata type vector. -/

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- Appending segments retains their payloads and code-visible types in the same order. -/
structure ElementsAdded (env result : metadata.ModuleMetadata metadata.CodeMetadata) (added : List metadata.Element) : Prop where
  fields : result = { env with elements := result.elements, code := { env.code with
    funcs := result.code.funcs, elem_segment_types := result.code.elem_segment_types } }
  elements : result.elements.val = env.elements.val ++ added
  types : result.code.elem_segment_types.val = env.code.elem_segment_types.val ++ added.map metadata.Element.elem
  refs : Module.References.Added env.code { env.code with funcs := result.code.funcs } (added.flatMap Module.References.element)

/-- An element is valid in the environment: its table, offset and initializers are valid. -/
abbrev ElementValid := Module.Segments.elementValid

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

private theorem element_valid_caches {env result entry}
    (h : ElementValid result entry)
    (hf : env.funcs.val.length = result.funcs.val.length) (hg : env.globals = result.globals)
    (hn : env.num_imported_globals = result.num_imported_globals)
    (ht : env.tables = result.tables) : ElementValid env entry := by
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
theorem metadata.decode_element_section_loop.spec (data : Slice U8) (env : metadata.ModuleMetadata metadata.CodeMetadata)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.elements.val.length ≤ start.val) (hrefs : env.code.elem_segment_types.val.length ≤ start.val) :
    metadata.decode_element_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ ElementsAdded env r.2 added ∧
          At (Rep ElementEncoding) data start (added.map Module.Environment.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env.code entry) ∧ r.2.elements.val.length ≤ next.val ∧
          r.2.code.elem_segment_types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_element_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      ElementsAdded env s.1 added ∧
      At (Rep ElementEncoding) data start (added.map Module.Environment.rawElement) s.2.1 ∧
      (∀ entry ∈ added, ElementValid env.code entry) ∧ s.1.elements.val.length ≤ s.2.1.val ∧
      s.1.code.elem_segment_types.val.length ≤ s.2.1.val)
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
        (metadata.decode_element.spec data pos current.code)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨entry, next⟩ := pair
        obtain ⟨hb, hadded, hv, hprogress⟩ := hp
        dsimp only at hadded
        have hspan := hb.span
        have htypes : updated.elem_segment_types = current.code.elem_segment_types := by rw [hadded.fields]
        have hcap : updated.elem_segment_types.val.length < Usize.max := by rw [htypes]; scalar_tac
        have hcap' : current.elements.val.length < Usize.max := by scalar_tac
        have hentry : ElementValid env.code entry := by
          apply element_valid_caches hv
          · have hx := congrArg List.length henv.refs.funcs
            simpa using hx.symm
          all_goals rw [henv.fields]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨types, ht⟩
        step as ⟨elements, helements⟩
        step as ⟨j,hj⟩
        refine ⟨by scalar_tac, ⟨added ++ [entry], by simp [hj, hlen], ?_, ?_, ?_, ?_, ?_⟩, by scalar_tac⟩
        · constructor
          · rw [hadded.fields, henv.fields]
          · simp [helements,henv.elements,List.append_assoc]
          · simp [ht,htypes,henv.types,List.append_assoc]
          · have hu : Module.References.Added {env.code with funcs := current.code.funcs}
                  {env.code with funcs := updated.funcs} (Module.References.element entry) := ⟨rfl,hadded.funcs⟩
            simpa using henv.refs.trans hu
        · simpa only [List.map_append, List.map_cons, List.map_nil, Module.Environment.rawElement]
            using hbytes.snoc hb
        · intro value hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hvalid value hm
          · simpa [List.mem_singleton.mp hm] using hentry
        · simp only [helements, List.length_append, List.length_singleton]
          omega
        · simp [ht,htypes]; omega
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp, by simp, Module.References.Added.refl _⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hsize, hrefs⟩

/-- `metadata.decode_element_section` adds the elements of a `VecEncoding` span, each
`ElementValid`. -/
@[step]
theorem metadata.decode_element_section.spec (data : Slice U8) (pos : Usize) (env : metadata.ModuleMetadata metadata.CodeMetadata)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.code.elem_segment_types.val.length ≤ pos.val) :
    metadata.decode_element_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, ElementsAdded env r.2 added ∧
          At (VecEncoding ElementEncoding) data pos (added.map Module.Environment.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env.code entry) ∧ r.2.elements.val.length ≤ next.val ∧
          r.2.code.elem_segment_types.val.length ≤ next.val
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
      (metadata.decode_element_section_loop.spec data env count start hs.2.2 (by omega) (by omega))
    simp [metadata.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize, hrefs⟩ := hp
      exact ⟨added, henv, At.vector hc hb (by simpa using hlen), ht, hsize, hrefs⟩

end Itasca
