import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Module.Env.Encoding
import Itasca.Module.Sections.EnvironmentAndTail
import Itasca.Module.Sections.Headers

/-!
# Requirements

Environment preservation, validity and source semantics establish the requirements consumed by module assembly. Cache and declaration witnesses remain tied to the same parsed environment.
-/

/-! ## Preservation -/

section

/-!
# Preservation along section runs

`Effect.represents` and `Run.represents` show that decoding sections keeps `Represents` between
the environment and the ghost declarations. `Effect.signature_bounded` and `Run.signature_bounded`
keep the signature bounds. `metadata.ModuleMetadataCodeMetadata.new.declarations` shows that the empty environment
starts all of these invariants, and `ImportsAdded.represents` covers the import section.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The extracted initial environment represents the empty declaration prefix, is valid and
bounded, and has phase `0`. -/
theorem metadata.ModuleMetadataCodeMetadata.new.declarations : metadata.ModuleMetadataCodeMetadata.new ⦃ env =>
    Module.Environment.Represents env {} ∧ Module.Environment.Valid env ∧
    Module.Environment.SignatureBounded env.code 0 ∧ Module.Environment.Bounded env 0 ∧ Module.Environment.Phase 0 {} ⦄ := by
  have h := metadata.ModuleMetadataCodeMetadata.new.spec
  simp only [metadata.ModuleMetadataCodeMetadata.new, metadata.CodeMetadata.new, bind_ok, WP.spec_ok] at h ⊢
  refine ⟨?_, h.2.1, ?_, h.2.2, ?_⟩
  · constructor <;> first | rfl | exact h.1
  · simp [Module.Environment.SignatureBounded]
  · simp [Module.Environment.Phase]

end Itasca

namespace Itasca.Module.Sections

theorem ImportsAdded.types {env entries result} (h : ImportsAdded env entries result) :
    result.code.types = env.code.types := by
  induction h with
  | nil => rfl
  | @snoc entries before after entry hp ha ih =>
      obtain ⟨_, hd⟩ := ha
      cases he : entry.desc <;> simp only [he] at hd
      all_goals first | rw [hd.1]; exact ih | rw [hd.2.1]; exact ih

open Module.Environment

/-- Adding one import appends it to the declared imports and keeps the environment representing
the declarations, provided no functions, globals, tables or memories are declared yet. -/
theorem ImportAdded.represents {env result entry decls}
    (h : ImportAdded env result entry) (hr : Represents env decls)
    (hf : decls.functions = []) (hg : decls.globals = [])
    (ht : decls.tables = []) (hm : decls.memories = []) :
    Represents result { decls with imports := decls.imports ++ [entry] } := by
  obtain ⟨⟨actual, hi, hrecord⟩, hd⟩ := h
  have himports : result.imports.val.map (fun i => (i.module.val, i.name.val, i.kind)) =
      (decls.imports ++ [entry]).map importRecord := by
    simp [hi, hr.imports, hrecord]
  obtain ⟨hfuncs, hnfuncs, hglobals, hnglobals, htables, hmemories⟩ := hr.cache
  cases he : entry.desc <;> simp only [he] at hd
  all_goals
    first | obtain ⟨_, hfields, hdesc, hcount⟩ := hd; guard_hyp hfields : result = _ | obtain ⟨hfields, hdesc, hcount⟩ := hd
    rw [hfields]
    refine ⟨hr.types, himports, hr.exports, hr.start, hr.elements, hr.elementTypes, hr.dataCount, ?_⟩
    clear hfields
    constructor <;>
      simp_all [importedFuncs, importedGlobals, importedTables, importedMems]

/-- Adding a vector of imports appends them to the declared imports and keeps the environment
representing the declarations. -/
theorem ImportsAdded.represents {env result entries decls}
    (h : ImportsAdded env entries result) (hr : Represents env decls)
    (hf : decls.functions = []) (hg : decls.globals = [])
    (ht : decls.tables = []) (hm : decls.memories = []) :
    Represents result { decls with imports := decls.imports ++ entries } := by
  induction h generalizing decls with
  | nil => simpa using hr
  | snoc hp ha ih =>
    have hr' := ih hr hf hg ht hm
    have hr'' := ha.represents hr' hf hg ht hm
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hr''

end Itasca.Module.Sections

namespace Itasca.Module.Environment

open Binary Module.Sections

/-- Every section preserves the bound on nested parameter vectors. Newly declared signatures obtain
their bound from their own byte span. -/
theorem Effect.signature_bounded {data pos env before id next result after}
    (h : Effect data pos env before id next result after) (hs : SignatureBounded env.code pos.val) :
    SignatureBounded result.code next.val := by
  have hm := hs.mono h.span.1
  cases h with
  | types ha hb _ => exact hs.of_types_added ha hb
  | imports ha _ => simpa only [SignatureBounded, ha.types] using hm
  | functions ha _ | tables ha _ _ | memories ha _ _ _ | globals ha _ _ =>
      rw [ha.1]; exact hm
  | exports ha hb =>
      clear hb
      have ht : result.code.types = env.code.types := by
        induction ha with
        | nil => rfl
        | @snoc _ before after entry _ ha ih =>
            have hm := ha.2.2.2
            cases he : entry.desc <;> simp only [Marked, he] at hm <;>
              obtain ⟨_, _, heq⟩ := hm <;> rw [heq] <;> exact ih
      simpa only [SignatureBounded, ht] using hm
  | start he _ _ | dataCount he _ => rw [he]; exact hm
  | elements ha _ _ => rw [ha.fields]; exact hm

theorem map_descriptor_update {α β : Type} (v : alloc.vec.Vec α) (idx : U32)
    {d replacement : α} (project : α → β) (lookup : v.val[idx.val]? = some d)
    (same : project replacement = project d) :
    (v.set (UScalar.cast .Usize idx) replacement).val.map project = v.val.map project := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_map, alloc.vec.Vec.set_val_eq, List.getElem_set]
    split <;> simp_all

private theorem marked_represents {env result decls entry}
    (h : ExportAdded env result entry) (hr : Represents env decls) :
    Represents result {decls with exports := decls.exports ++ [rawExport entry]} := by
  obtain ⟨fields, exports, _, marked⟩ := h
  rw [fields]
  have hx : decls.exports ++ [rawExport entry] = result.exports.val.map rawExport := by
    simp [exports, hr.exports]
  cases he : entry.desc <;> simp only [Marked, he] at marked <;>
    obtain ⟨d, lookup, update⟩ := marked <;> rw [update]
  all_goals
    refine ⟨hr.types, hr.imports, hx, hr.start, hr.elements, hr.elementTypes, hr.dataCount, ?_⟩
    constructor <;> try first
      | exact hr.cache.funcs
      | exact hr.cache.numFuncs
      | exact hr.cache.globalEntries
      | exact hr.cache.numGlobals
      | exact hr.cache.tableEntries
      | exact hr.cache.memoryEntries
    all_goals
      dsimp only
      first | rw [← hr.cache.funcs] | rw [← hr.cache.tableEntries] |
        rw [← hr.cache.memoryEntries] | rw [← hr.cache.globalEntries]
      exact map_descriptor_update _ _ _ lookup rfl

private theorem exports_represents {env result decls entries}
    (h : ExportsAdded env entries result) (hr : Represents env decls) :
    Represents result {decls with exports := decls.exports ++ entries.map rawExport} := by
  induction h with
  | nil => simpa using hr
  | snoc _ ha ih => simpa [List.append_assoc] using marked_represents ha ih

/-- A section update in increasing section order keeps the environment representing the
declarations, including the merged index-space caches. -/
theorem Effect.represents {data pos env before id next result after last}
    (h : Effect data pos env before id next result after) (hr : Represents env before)
    (hp : Phase last before) (horder : last < (sectionRank id).val) : Represents result after := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  cases h with
  | imports ha hb =>
    change last < 2 at horder
    have hi := ha.represents hr (h3 (by omega)) (h6 (by omega))
      (h4 (by omega)) (h5 (by omega))
    simpa only [h2 horder, List.nil_append] using hi
  | exports ha _ =>
    change last < 7 at horder
    simpa only [h7 horder, List.nil_append] using exports_represents ha hr
  | types ha _ _ =>
    change last < 1 at horder
    rw [ha.1]
    refine ⟨?_, hr.imports, hr.exports, hr.start, hr.elements, hr.elementTypes, hr.dataCount, ?_⟩
    · simp [ha.2, ← hr.types, h1 horder]
    · exact ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globalEntries, hr.cache.numGlobals,
        hr.cache.tableEntries, hr.cache.memoryEntries⟩
  | functions ha _ | tables ha _ _ | memories ha _ _ _ | globals ha _ _ =>
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.exports, hr.start, hr.elements, hr.elementTypes, hr.dataCount, ?_⟩
    constructor <;> try first
      | exact hr.cache.funcs
      | exact hr.cache.numFuncs
      | exact hr.cache.globalEntries
      | exact hr.cache.numGlobals
      | exact hr.cache.tableEntries
      | exact hr.cache.memoryEntries
    all_goals dsimp only
    all_goals first
      | change last < 3 at horder; simp [ha.2.1, List.map_map, hr.cache.funcs, h3 horder, Function.comp_def]
      | change last < 4 at horder; simp [ha.2, List.map_map, hr.cache.tableEntries, h4 horder, Function.comp_def]
      | change last < 5 at horder; simp [ha.2, List.map_map, hr.cache.memoryEntries, h5 horder, Function.comp_def]
      | change last < 6 at horder
        first
          | rw [← hr.cache.funcs, ha.2.2.funcs]; apply List.ext_getElem <;> simp
          | simp [ha.2.1, List.map_map, hr.cache.globalEntries, h6 horder, Function.comp_def]
  | start he _ hv =>
    rw [he]
    refine ⟨hr.types, hr.imports, hr.exports, rfl, hr.elements, hr.elementTypes, hr.dataCount,
      ⟨?_, hr.cache.numFuncs, hr.cache.globalEntries, hr.cache.numGlobals, hr.cache.tableEntries, hr.cache.memoryEntries⟩⟩
    apply Eq.trans _ hr.cache.funcs
    exact map_descriptor_update _ _ _ hv.1 rfl
  | elements ha _ _ =>
    change last < 9 at horder
    rw [ha.fields]
    refine ⟨hr.types, hr.imports, hr.exports, hr.start, ?_, ?_, hr.dataCount,
      ⟨?_, hr.cache.numFuncs, hr.cache.globalEntries, hr.cache.numGlobals, hr.cache.tableEntries, hr.cache.memoryEntries⟩⟩
    · simp [ha.elements, ← hr.elements, h9 horder]
    · simp [ha.types, hr.elementTypes, h9 horder, List.map_map, rawElement, Function.comp_def]
    · dsimp only
      rw [← hr.cache.funcs, ha.refs.funcs]
      apply List.ext_getElem <;> simp
  | dataCount he _ =>
    rw [he]
    exact ⟨hr.types, hr.imports, hr.exports, hr.start, hr.elements, hr.elementTypes, rfl,
      ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globalEntries, hr.cache.numGlobals,
       hr.cache.tableEntries, hr.cache.memoryEntries⟩⟩

/-- A run of sections keeps the environment representing the declarations. -/
theorem Run.represents {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hp : Phase initialId.val decls) :
    Represents after afterDecls := by
  induction h with
  | nil => exact hr
  | custom _ _ ih => exact ih
  | step previous horder hh he ih => exact he.represents ih (previous.phase hp) horder

/-- A run of sections keeps the signature bound. -/
theorem Run.signature_bounded {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hs : SignatureBounded initial.code start.val) : SignatureBounded after.code next.val := by
  induction h with
  | nil => exact hs
  | custom _ hb ih => exact ih.mono hb.span.1
  | step _ horder hh he ih => exact he.signature_bounded (ih.mono (Nat.le_of_lt hh.span.1))

end Itasca.Module.Environment

end
