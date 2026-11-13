import Itasca.Module.Env.TypeBounds
import Itasca.Module.Sections.Imports
import Itasca.Module.Sections.Table
import Itasca.Module.Sections.Memory
import Itasca.Module.Sections.Global
import Itasca.Module.Sections.Element
import Itasca.Module.Sections.Export
import Itasca.Module.Sections.DataCount

/-!
# Per-section effects

`Effect` relates one declaration section to its effect: the section's independent payload
encoding, the checked update of the environment, and the update of the `Declarations` record.
`Effect.phase` shows that an effect advances the section phase.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary ModuleSections

/-- Decoding the section with id `id` at `pos` takes `env` to `result` and `before` to the final
declarations, ending at `next`. Each constructor pairs the payload encoding with the section's
checked environment update. Emptiness of later sections distinguishes an initial declaration
vector from an append performed by the extracted parser. -/
inductive Effect (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (before : Declarations) : U8 → Usize → metadata.Env → Declarations →
      Prop where
  | types {result next added} : TypesAdded env result added →
      At (VecEncoding FuncTypeEncoding) data pos added next →
      (∀ ft ∈ added, Profile.FuncTypeAdmissible ft) →
      Effect data pos env before 1#u8 next result {before with types := added}
  | imports {result next added} : ImportsAdded env added result →
      At (VecEncoding ImportEncoding) data pos (added.map rawImport) next →
      Effect data pos env before 2#u8 next result {before with imports := added.map rawImport}
  | functions {result next indices signatures} : FunctionsAdded env result indices signatures →
      At (VecEncoding IndexEncoding) data pos indices next →
      Effect data pos env before 3#u8 next result {before with functions := indices}
  | tables {result next added} : TablesAdded env result added →
      At (VecEncoding TableTypeEncoding) data pos added next →
      (∀ tt ∈ added, ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1)) →
      Effect data pos env before 4#u8 next result {before with tables := added}
  | memories {result next added} : MemoriesAdded env result added →
      At (VecEncoding MemTypeEncoding) data pos added next →
      (∀ mt ∈ added, ModuleTranslation.LimitsValid mt.limits (2 ^ 16)) →
      result.mem_types.val.length ≤ max env.mem_types.val.length 1 →
      Effect data pos env before 5#u8 next result {before with memories := added}
  | globals {result next added} : GlobalsAdded env result added →
      At (VecEncoding GlobalEncoding) data pos added next →
      (∀ g ∈ added, ModuleConstants.Valid result g.init g.gtype.valtype) →
      Effect data pos env before 6#u8 next result {before with globals := added}
  | exports {result next added} : ExportsAdded env added result →
      At (VecEncoding ExportEncoding) data pos (added.map rawExport) next →
      Effect data pos env before 7#u8 next result {before with exports := added.map rawExport}
  | start {result next idx} : result = {env with start := some idx} →
      At StartEncoding data pos (some idx) next →
      (∃ hi : idx.val < env.func_types.val.length,
        env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []) →
      Effect data pos env before 8#u8 next result {before with start := some idx}
  | elements {result next added} : ElementsAdded env result added →
      At (VecEncoding (ElementEncodingFor)) data pos (added.map rawElement) next →
      (∀ entry ∈ added, ElementValid env entry) →
      Effect data pos env before 9#u8 next result {before with elements := added.map rawElement}
  | dataCount {result next count} : result = {env with data_count := some count} →
      At StartEncoding data pos (some count) next →
      Effect data pos env before 12#u8 next result
        { before with dataCount := some count }

theorem Effect.span {data pos env before id next result after}
    (h : Effect data pos env before id next result after) :
    pos.val ≤ next.val ∧ next.val ≤ data.length := by
  cases h <;> apply At.span <;> assumption

/-- A section effect in increasing section order advances the phase to that section's rank. -/
theorem Effect.phase {data pos env before id next result after last}
    (h : Effect data pos env before id next result after)
    (hp : Phase last before) (horder : last < (sectionRank id).val) : Phase (sectionRank id).val after := by
  rcases hp with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  cases h <;> simp [Phase, sectionRank] at *
  all_goals repeat' constructor
  all_goals first | omega | exact h1 (by omega) | exact h2 (by omega) |
    exact h3 (by omega) | exact h4 (by omega) | exact h5 (by omega) |
    exact h6 (by omega) | exact h7 (by omega) | exact h8 (by omega) | exact h9 (by omega) | exact h10 (by omega)

end Itasca.ModuleEnv
