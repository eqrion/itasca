import Itasca.Module.Env.Run
import Itasca.Module.Env.NameFacts

/-!
# Preservation along section runs

`Effect.represents` and `Run.represents` show that decoding sections keeps `Represents` between
the environment and the ghost declarations. `Effect.signatureBounded` and `Run.signatureBounded`
keep the signature bounds. `module.Env.new.profile_declarations` shows that the empty environment
starts all of these invariants, and `ImportsAdded.represents` covers the import section.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The extracted initial environment represents the empty declaration prefix, is valid and
bounded, and has phase `0`. -/
theorem module.Env.new.profile_declarations (profile : ValidationProfile) : module.Env.new ⦃ env =>
    ModuleEnv.Represents env {} ∧ ModuleEnv.Valid env profile ∧
    ModuleEnv.SignatureBounded env 0 ∧ ModuleEnv.Bounded env 0 ∧ ModuleEnv.Phase 0 {} ⦄ := by
  unfold module.Env.new
  simp only [WP.spec_ok]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> try rfl
    constructor <;> simp [ModuleEnv.importedFuncs, ModuleEnv.importedGlobals,
      ModuleEnv.importedTables, ModuleEnv.importedMems]
  · constructor <;> simp [ModuleReferences.Coherent, ModuleReferences.collected]
  · simp [ModuleEnv.SignatureBounded]
  · constructor <;> simp
  · simp [ModuleEnv.Phase]

/-- `module.Env.new.profile_declarations` for Wasm 1.0. -/
theorem module.Env.new.declarations : module.Env.new ⦃ env =>
    ModuleEnv.Represents env {} ∧ ModuleEnv.Valid env ∧
    ModuleEnv.SignatureBounded env 0 ∧ ModuleEnv.Bounded env 0 ∧ ModuleEnv.Phase 0 {} ⦄ :=
  module.Env.new.profile_declarations .Wasm1

end Itasca

namespace Itasca.ModuleSections

theorem ImportsAdded.types {profile} {env entries result} (h : ImportsAdded env entries result profile) :
    result.types = env.types := by
  induction h with
  | nil => rfl
  | @snoc profile entries before after entry hp ha ih =>
      obtain ⟨_, ha⟩ := ha
      cases hd : entry.desc <;> simp only [hd] at ha
      · obtain ⟨_, _, he, _⟩ := ha
        have ht := congrArg module.Env.types he
        change after.types = before.types at ht
        exact ht.trans ih
      · have ht := congrArg module.Env.types ha.1
        change after.types = before.types at ht
        exact ht.trans ih
      · have ht := congrArg module.Env.types ha.1
        change after.types = before.types at ht
        exact ht.trans ih
      · have ht := congrArg module.Env.types ha.1
        change after.types = before.types at ht
        exact ht.trans ih


open ModuleEnv

/-- Adding one import appends it to the declared imports and keeps the environment representing
the declarations, provided no functions, globals, tables or memories are declared yet. -/
theorem ImportAdded.represents {profile} {env result entry decls}
    (h : ImportAdded env result entry profile) (hr : Represents env decls)
    (hf : decls.functions = []) (hg : decls.globals = [])
    (ht : decls.tables = []) (hm : decls.memories = []) :
    Represents result { decls with imports := decls.imports ++ [rawImport entry] } := by
  have hidx : env.func_type_indices.val = [] := hr.functions.symm.trans hf
  have hglobals : env.globals.val = [] := hr.globals.symm.trans hg
  obtain ⟨hi, hd⟩ := h
  cases he : entry.desc <;> simp only [he] at hd
  · obtain ⟨ft, hresolve, henv, hfuncs, hnum⟩ := hd
    rw [henv]
    refine ⟨hr.types, ?_, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · simp only [hi, List.map_append, List.map_cons, List.map_nil, hr.imports]
    · constructor
      · simpa [importedFuncs, hi, he, hidx, hfuncs] using
          List.rel_append hr.cache.funcs (List.Forall₂.cons hresolve .nil)
      · simpa [importedFuncs, hi, he, hnum] using hr.cache.numFuncs
      · simpa [importedGlobals, hi, he] using hr.cache.globals
      · simpa [importedGlobals, hi, he] using hr.cache.numGlobals
      · simpa [importedTables, hi, he] using hr.cache.tables
      · simpa [importedMems, hi, he] using hr.cache.memories
  · rename_i tt
    obtain ⟨henv, htables, _, _⟩ := hd
    rw [henv]
    refine ⟨hr.types, ?_, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · simp only [hi, List.map_append, List.map_cons, List.map_nil, hr.imports]
    · constructor
      · simpa [importedFuncs, hi, he] using hr.cache.funcs
      · simpa [importedFuncs, hi, he] using hr.cache.numFuncs
      · simpa [importedGlobals, hi, he] using hr.cache.globals
      · simpa [importedGlobals, hi, he] using hr.cache.numGlobals
      · simpa [importedTables, hi, he, htables, ht] using congrArg (· ++ [tt]) hr.cache.tables
      · simpa [importedMems, hi, he] using hr.cache.memories
  · rename_i mt
    obtain ⟨henv, hmemories, _, _⟩ := hd
    rw [henv]
    refine ⟨hr.types, ?_, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · simp only [hi, List.map_append, List.map_cons, List.map_nil, hr.imports]
    · constructor
      · simpa [importedFuncs, hi, he] using hr.cache.funcs
      · simpa [importedFuncs, hi, he] using hr.cache.numFuncs
      · simpa [importedGlobals, hi, he] using hr.cache.globals
      · simpa [importedGlobals, hi, he] using hr.cache.numGlobals
      · simpa [importedTables, hi, he] using hr.cache.tables
      · simpa [importedMems, hi, he, hmemories, hm] using congrArg (· ++ [mt]) hr.cache.memories
  · rename_i gt
    obtain ⟨henv, htypes, hnum, _⟩ := hd
    rw [henv]
    refine ⟨hr.types, ?_, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · simp only [hi, List.map_append, List.map_cons, List.map_nil, hr.imports]
    · constructor
      · simpa [importedFuncs, hi, he] using hr.cache.funcs
      · simpa [importedFuncs, hi, he] using hr.cache.numFuncs
      · simpa [importedGlobals, hi, he, hglobals, htypes] using congrArg (· ++ [gt]) hr.cache.globals
      · simpa [importedGlobals, hi, he, hnum] using hr.cache.numGlobals
      · simpa [importedTables, hi, he] using hr.cache.tables
      · simpa [importedMems, hi, he] using hr.cache.memories

/-- Adding a vector of imports appends them to the declared imports and keeps the environment
representing the declarations. -/
theorem ImportsAdded.represents {profile} {env result entries decls}
    (h : ImportsAdded env entries result profile) (hr : Represents env decls)
    (hf : decls.functions = []) (hg : decls.globals = [])
    (ht : decls.tables = []) (hm : decls.memories = []) :
    Represents result { decls with imports := decls.imports ++ entries.map rawImport } := by
  induction h generalizing decls with
  | nil => simpa using hr
  | snoc hp ha ih =>
    have hr' := ih hr hf hg ht hm
    have hr'' := ha.represents hr' hf hg ht hm
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hr''

end Itasca.ModuleSections

namespace Itasca.ModuleEnv

open ModuleBinary ModuleSections

/-- Every section preserves the bound on nested parameter vectors. Newly declared signatures obtain
their bound from their own byte span. -/
theorem Effect.signatureBounded {profile} {data pos env before id next result after}
    (h : Effect (profile := profile) data pos env before id next result after) (hs : SignatureBounded env pos.val) :
    SignatureBounded result next.val := by
  have hspan := h.span
  have hm := hs.mono hspan.1
  cases h with
  | types ha hb hv => exact hs.of_types_added ha hb
  | imports ha hb => simpa only [SignatureBounded, ha.types] using hm
  | functions ha hb =>
      have ht := congrArg module.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | tables ha hb hv hc =>
      have ht := congrArg module.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | memories ha hb hv hc =>
      have ht := congrArg module.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | globals ha hb hv =>
      have ht := congrArg module.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | exports ha hb =>
      have ht := congrArg module.Env.types ha.unchanged
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | start he hb hv => simpa only [SignatureBounded, he] using hm
  | elements ha hb hv =>
      have ht := congrArg module.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm

  | dataCount hp he hb => simpa only [SignatureBounded, he] using hm


/-- A section update in increasing section order keeps the environment representing the
declarations, including the merged index-space caches. -/
theorem Effect.represents {profile} {data pos env before id next result after last}
    (h : Effect (profile := profile) data pos env before id next result after) (hr : Represents env before)
    (hp : Phase last before) (horder : last < (sectionRank id).val) : Represents result after := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  cases h with
  | types ha hb hv =>
    change last < 1 at horder
    have ht := h1 (by simpa using horder)
    have hi : env.imports.val = [] := by
      have he := hr.imports.symm.trans (h2 (by scalar_tac))
      simpa using he
    have hidx : env.func_type_indices.val = [] := hr.functions.symm.trans (h3 (by scalar_tac))
    have hfuncs : env.func_types.val = [] := by
      have hl := hr.cache.funcs.length_eq
      simpa [importedFuncs, hi, hidx] using hl.symm
    rw [ha.1]
    refine ⟨?_, hr.imports, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.2, ← hr.types, ht, List.nil_append]
    · constructor
      · simp [importedFuncs, hi, hidx, hfuncs]
      · exact hr.cache.numFuncs
      · exact hr.cache.globals
      · exact hr.cache.numGlobals
      · exact hr.cache.tables
      · exact hr.cache.memories
  | imports ha hb =>
    change last < 2 at horder
    have hi := ha.represents hr (h3 (by scalar_tac)) (h6 (by scalar_tac))
      (h4 (by scalar_tac)) (h5 (by scalar_tac))
    simpa only [h2 (by scalar_tac), List.nil_append] using hi
  | functions ha hb =>
    change last < 3 at horder
    have hf := h3 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, ?_, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.2.1, ← hr.functions, hf, List.nil_append]
    · constructor
      · simpa only [ha.2.1, ha.2.2.1, List.append_assoc] using
          List.rel_append hr.cache.funcs ha.2.2.2
      · exact hr.cache.numFuncs
      · exact hr.cache.globals
      · exact hr.cache.numGlobals
      · exact hr.cache.tables
      · exact hr.cache.memories
  | tables ha hb hv hc =>
    change last < 4 at horder
    have ht := h4 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    constructor
    · exact hr.cache.funcs
    · exact hr.cache.numFuncs
    · exact hr.cache.globals
    · exact hr.cache.numGlobals
    · dsimp only
      rw [ha.2, hr.cache.tables, ht, List.append_nil]
    · exact hr.cache.memories
  | memories ha hb hv hc =>
    change last < 5 at horder
    have hm := h5 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    constructor
    · exact hr.cache.funcs
    · exact hr.cache.numFuncs
    · exact hr.cache.globals
    · exact hr.cache.numGlobals
    · exact hr.cache.tables
    · dsimp only
      rw [ha.2, hr.cache.memories, hm, List.append_nil]
  | globals ha hb hv =>
    change last < 6 at horder
    have hg := h6 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.functions, ?_, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.2.1, ← hr.globals, hg, List.nil_append]
    · constructor
      · exact hr.cache.funcs
      · exact hr.cache.numFuncs
      · dsimp only
        rw [ha.2.1, ha.2.2.1, hr.cache.globals, List.map_append, List.append_assoc]
      · exact hr.cache.numGlobals
      · exact hr.cache.tables
      · exact hr.cache.memories
  | exports ha hb =>
    change last < 7 at horder
    have he := h7 (by simpa using horder)
    rw [ha.unchanged]
    refine ⟨hr.types, hr.imports, hr.functions, hr.globals, ?_, hr.start, hr.elements, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.exports, List.map_append, ← hr.exports, he, List.nil_append]
    · exact ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globals, hr.cache.numGlobals, hr.cache.tables, hr.cache.memories⟩
  | start he hb hv =>
    change last < 8 at horder
    rw [he]
    exact ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, rfl, hr.elements, hr.dataCount, ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globals, hr.cache.numGlobals, hr.cache.tables, hr.cache.memories⟩⟩
  | elements ha hb hv =>
    change last < 9 at horder
    have he := h9 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, hr.start, ?_, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.2.1, List.map_append, ← hr.elements, he, List.nil_append]
    · exact ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globals, hr.cache.numGlobals, hr.cache.tables, hr.cache.memories⟩

  | dataCount hp he hb =>
    rw [he]
    exact ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, hr.start,
      hr.elements, rfl, ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globals,
      hr.cache.numGlobals, hr.cache.tables, hr.cache.memories⟩⟩


/-- A run of sections keeps the environment representing the declarations. -/
theorem Run.represents {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hp : Phase initialId.val decls) :
    Represents after afterDecls := by
  induction h with
  | nil => exact hr
  | custom _ _ ih => exact ih
  | step previous horder hh he ih => exact he.represents ih (previous.phase hp) horder

/-- A run of sections keeps the signature bound. -/
theorem Run.signatureBounded {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hs : SignatureBounded initial start.val) : SignatureBounded after next.val := by
  induction h with
  | nil => exact hs
  | custom _ hb ih => exact ih.mono hb.span.1
  | step _ horder hh he ih => exact he.signatureBounded (ih.mono (Nat.le_of_lt hh.span.1))

end Itasca.ModuleEnv
