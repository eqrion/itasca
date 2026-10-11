import Itasca.Module.ModuleTypeBounds
import Itasca.Module.ModuleImportSection
import Itasca.Module.ModuleTableSection
import Itasca.Module.ModuleMemorySection
import Itasca.Module.ModuleGlobalSection
import Itasca.Module.ModuleElements
import Itasca.Module.ModuleExports

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary ModuleSections

/-- Each section has an independent payload encoding and a checked semantic
state update. Later-section emptiness supplies the distinction between an
initial declaration vector and an append performed by the extracted parser. -/
inductive Effect (data : Slice U8) (pos : Usize) (env : module.Env)
    (before : Declarations) : U8 → Usize → module.Env → Declarations →
      (profile : optParam ValidationProfile .Wasm1) → Prop where
  | types {profile} {result next added} : TypesAdded env result added →
      At (VecEncoding FuncTypeEncoding) data pos added next →
      (∀ ft ∈ added, Profile.FuncTypeAdmissible profile ft) →
      Effect (profile := profile) data pos env before 1#u8 next result { before with types := added }
  | imports {profile} {result next added} : ImportsAdded env added result →
      At (VecEncoding ImportEncoding) data pos (added.map rawImport) next →
      Effect (profile := profile) data pos env before 2#u8 next result { before with imports := added.map rawImport }
  | functions {profile} {result next indices signatures} : FunctionsAdded env result indices signatures →
      At (VecEncoding IndexEncoding) data pos indices next →
      Effect (profile := profile) data pos env before 3#u8 next result { before with functions := indices }
  | tables {profile} {result next added} : TablesAdded env result added →
      At (VecEncoding TableTypeEncoding) data pos added next →
      (∀ tt ∈ added, ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1)) →
      result.table_types.val.length ≤ max env.table_types.val.length 1 →
      Effect (profile := profile) data pos env before 4#u8 next result { before with tables := added }
  | memories {profile} {result next added} : MemoriesAdded env result added →
      At (VecEncoding MemTypeEncoding) data pos added next →
      (∀ mt ∈ added, ModuleTranslation.LimitsValid mt.limits (2 ^ 16)) →
      result.mem_types.val.length ≤ max env.mem_types.val.length 1 →
      Effect (profile := profile) data pos env before 5#u8 next result { before with memories := added }
  | globals {profile} {result next added} : GlobalsAdded env result added →
      At (VecEncoding GlobalEncoding) data pos added next →
      (∀ g ∈ added, ModuleConstants.Valid result g.init g.gtype.valtype) →
      Effect (profile := profile) data pos env before 6#u8 next result { before with globals := added }
  | exports {profile} {result next added} : ExportsAdded env added result →
      At (VecEncoding ExportEncoding) data pos (added.map rawExport) next →
      Effect (profile := profile) data pos env before 7#u8 next result { before with exports := added.map rawExport }
  | start {profile} {result next idx} : result = { env with start := some idx } →
      At StartEncoding data pos (some idx) next →
      (∃ hi : idx.val < env.func_types.val.length,
        env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []) →
      Effect (profile := profile) data pos env before 8#u8 next result { before with start := some idx }
  | elements {profile} {result next added} : ElementsAdded env result added →
      At (VecEncoding (ElementEncodingFor profile)) data pos (added.map rawElement) next →
      (∀ entry ∈ added, ElementValid env entry) →
      Effect (profile := profile) data pos env before 9#u8 next result { before with elements := added.map rawElement }

theorem Effect.span {profile} {data pos env before id next result after}
    (h : Effect (profile := profile) data pos env before id next result after) :
    pos.val ≤ next.val ∧ next.val ≤ data.length := by
  cases h <;> apply At.span <;> assumption

theorem Effect.id_range {profile} {data pos env before id next result after}
    (h : Effect (profile := profile) data pos env before id next result after) : 1 ≤ id.val ∧ id.val ≤ 9 := by
  cases h <;> decide

/-- This phase condition excludes duplicate sections and keeps future raw fields empty. -/
def Phase (last : Nat) (decls : Declarations) : Prop :=
  (last < 1 → decls.types = []) ∧
  (last < 2 → decls.imports = []) ∧
  (last < 3 → decls.functions = []) ∧
  (last < 4 → decls.tables = []) ∧
  (last < 5 → decls.memories = []) ∧
  (last < 6 → decls.globals = []) ∧
  (last < 7 → decls.exports = []) ∧
  (last < 8 → decls.start = none) ∧
  (last < 9 → decls.elements = [])

theorem Effect.phase {profile} {data pos env before id next result after last}
    (h : Effect (profile := profile) data pos env before id next result after)
    (hp : Phase last before) (horder : last < id.val) : Phase id.val after := by
  rcases hp with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  cases h <;> simp [Phase] at *
  all_goals repeat' constructor
  all_goals first | omega | exact h1 (by omega) | exact h2 (by omega) |
    exact h3 (by omega) | exact h4 (by omega) | exact h5 (by omega) |
    exact h6 (by omega) | exact h7 (by omega) | exact h8 (by omega) | exact h9 (by omega)

end Itasca.ModuleEnv
