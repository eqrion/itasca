import Itasca.Module.Env.TypeBounds
import Itasca.Module.Sections.Imports
import Itasca.Module.Sections.Table
import Itasca.Module.Sections.Memory
import Itasca.Module.Sections.Global
import Itasca.Module.Sections.Element
import Itasca.Module.Sections.Export
import Itasca.Module.Sections.DataCount

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
      (∀ ft ∈ added, Profile.FuncTypeAdmissible profile ft ∧
        ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty) →
      Effect (profile := profile) data pos env before 1#u8 next result { before with types := added }
  | imports {profile} {result next added} : ImportsAdded env added result profile →
      At (VecEncoding ImportEncoding) data pos (added.map rawImport) next →
      Effect (profile := profile) data pos env before 2#u8 next result { before with imports := added.map rawImport }
  | functions {profile} {result next indices signatures} : FunctionsAdded env result indices signatures →
      At (VecEncoding IndexEncoding) data pos indices next →
      Effect (profile := profile) data pos env before 3#u8 next result { before with functions := indices }
  | tables {profile} {result next added} : TablesAdded env result added →
      At (VecEncoding TableTypeEncoding) data pos added next →
      (∀ tt ∈ added, ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1) ∧ ElemTypeAllowed profile tt.elem) →
      (profile = .Wasm1 → result.table_types.val.length ≤ max env.table_types.val.length 1) →
      Effect (profile := profile) data pos env before 4#u8 next result { before with tables := added }
  | memories {profile} {result next added} : MemoriesAdded env result added →
      At (VecEncoding MemTypeEncoding) data pos added next →
      (∀ mt ∈ added, ModuleTranslation.LimitsValid mt.limits (2 ^ 16)) →
      result.mem_types.val.length ≤ max env.mem_types.val.length 1 →
      Effect (profile := profile) data pos env before 5#u8 next result { before with memories := added }
  | globals {profile} {result next added} : GlobalsAdded env result added →
      At (VecEncoding GlobalEncoding) data pos added next →
      (∀ g ∈ added, ModuleConstants.Valid result g.init g.gtype.valtype ∧ ValueTypeAllowed profile g.gtype.valtype) →
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
  | dataCount {profile} {result next count} : profile = .Wasm2 →
      result = { env with data_count := some count } →
      At StartEncoding data pos (some count) next →
      Effect (profile := profile) data pos env before 12#u8 next result
        { before with dataCount := some count }

theorem Effect.span {profile} {data pos env before id next result after}
    (h : Effect (profile := profile) data pos env before id next result after) :
    pos.val ≤ next.val ∧ next.val ≤ data.length := by
  cases h <;> apply At.span <;> assumption

theorem Effect.id_range {profile} {data pos env before id next result after}
    (h : Effect (profile := profile) data pos env before id next result after) : 1 ≤ (sectionRank id).val ∧ (sectionRank id).val ≤ 10 := by
  cases h <;> decide

/-- Decoded section transitions retain the selected profile's type guards. -/
theorem Effect.allowed {profile data pos env before id next result after}
    (h : Effect data pos env before id next result after profile)
    (hb : ModuleTypesAllowed profile (before.module [] [])) :
    ModuleTypesAllowed profile (after.module [] []) := by
  rcases hb with ⟨ht, hi, htable, hg, hc, he, hd⟩
  cases h with
  | types ha hbytes hv =>
    exact ⟨fun ft hm => (hv ft hm).2, hi, htable, hg, hc, he, hd⟩
  | imports ha hbytes =>
    refine ⟨ht, ?_, htable, hg, hc, he, hd⟩
    intro entry hm
    obtain ⟨actual, hactual, rfl⟩ := List.mem_map.mp hm
    exact ha.allowed actual hactual
  | functions => exact ⟨ht, hi, htable, hg, hc, he, hd⟩
  | tables ha hbytes hv hcount =>
    exact ⟨ht, hi, fun tt hm => (hv tt hm).2, hg, hc, he, hd⟩
  | memories => exact ⟨ht, hi, htable, hg, hc, he, hd⟩
  | globals ha hbytes hv =>
    exact ⟨ht, hi, htable, fun g hm => ⟨(hv g hm).2, (hv g hm).1.const_allowed (hv g hm).2⟩, hc, he, hd⟩
  | exports => exact ⟨ht, hi, htable, hg, hc, he, hd⟩
  | start => exact ⟨ht, hi, htable, hg, hc, he, hd⟩
  | elements ha hbytes hv =>
    refine ⟨ht, hi, htable, hg, hc, ?_, hd⟩
    intro entry hm
    obtain ⟨actual, hactual, rfl⟩ := List.mem_map.mp hm
    have helem := (hv actual hactual).1
    cases hmode : actual.mode with
    | Passive => simp [rawElement, hmode]
    | Declarative => simp [rawElement, hmode]
    | Active idx offset =>
      obtain ⟨hidx, htable, hoff⟩ := (show ∃ hi : idx.val < env.table_types.val.length,
        env.table_types.val[idx.val].elem = actual.elem ∧ ModuleConstants.Valid env offset .I32 from by simpa [hmode] using helem)
      simpa only [rawElement, hmode] using hoff.const_allowed
        (show ValueTypeAllowed profile .I32 from by cases profile <;> trivial)
  | dataCount => exact ⟨ht, hi, htable, hg, hc, he, hd⟩

theorem Effect.phase {profile} {data pos env before id next result after last}
    (h : Effect (profile := profile) data pos env before id next result after)
    (hp : Phase last before) (horder : last < (sectionRank id).val) : Phase (sectionRank id).val after := by
  rcases hp with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  cases h <;> simp [Phase, sectionRank] at *
  all_goals repeat' constructor
  all_goals first | omega | exact h1 (by omega) | exact h2 (by omega) |
    exact h3 (by omega) | exact h4 (by omega) | exact h5 (by omega) |
    exact h6 (by omega) | exact h7 (by omega) | exact h8 (by omega) | exact h9 (by omega) | exact h10 (by omega)

end Itasca.ModuleEnv
