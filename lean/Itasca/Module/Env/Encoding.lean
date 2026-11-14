import Itasca.Module.Env.Declarations
import Itasca.Module.Sections.Tail
import Itasca.Module.Sections.Data
import Itasca.Module.Sections.ElementHeader
import Itasca.Module.Readers.Utf8
import Itasca.Binary.UnicodeUnique

/-!
Sections, each formerly its own module: Effects, Run, Dispatch, Parser, NameFacts, Encoding.
-/

/-! ## Effects -/

section

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

end

/-! ## Run -/

section

/-!
# Ordered section runs

`Run` is the history of sections decoded by the environment loop, each with its byte span and
`Effect`, in strictly increasing section order. Custom sections may appear between them.
`Run.phase`, `Run.span` and `Run.id_bounds` give the phase, byte-span and rank facts of a run.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- An ordered history of decoded sections from the initial environment and declarations to the
final ones, ending at position `next` after a section of rank `id`. It records bytes and semantic
changes rather than calls to the extracted parser. -/
inductive Run (data : Slice U8) (initial : metadata.Env) (decls : Declarations)
    (start : Usize) (initialId : U8) : metadata.Env → Declarations → Usize → U8 →
      Prop where
  | nil : Run data initial decls start initialId initial decls start initialId
  | custom {before beforeDecls pos last next} :
      Run data initial decls start initialId before beforeDecls pos last →
      ModuleBinary.At (fun (_ : Unit) => ModuleBinary.CustomEncoding) data pos () next →
      Run data initial decls start initialId before beforeDecls next last
  | step {before beforeDecls pos last id first next after afterDecls} :
      Run data initial decls start initialId before beforeDecls pos last →
      last.val < (ModuleBinary.sectionRank id).val →
      ModuleBinary.SectionHeader data pos id first next →
      Effect data first before beforeDecls id next after afterDecls →
      Run data initial decls start initialId after afterDecls next (ModuleBinary.sectionRank id)

/-- A run keeps the declarations in phase, ending at the last section's rank. -/
theorem Run.phase {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hp : Phase initialId.val decls) : Phase id.val afterDecls := by
  induction h with
  | nil => exact hp
  | custom _ _ ih => exact ih
  | step _ horder _ he ih => exact he.phase ih horder

/-- A run advances the position within the input. -/
theorem Run.span {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hstart : start.val ≤ data.length) : start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil => exact ⟨le_rfl, hstart⟩
  | custom _ hb ih => have := hb.span; omega
  | step _ _ hh _ ih => have := hh.span; omega

end Itasca.ModuleEnv

end

/-! ## Dispatch -/

section

/-!
# Section dispatch soundness

Specification of `metadata.decode_env_section`, which dispatches on a section id to the per-section
decoders. `metadata.decode_env_section.profile_spec` shows that every recognized section terminates,
preserves the `Bounded` invariant, and on success yields the `Effect` of its section. The
completeness counterpart is in `Module/Env/DispatchComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections ModuleEnv

/-- `metadata.decode_env_section` terminates for every section id, preserves `Bounded`, and on
success returns the `Effect` that relates the section's bytes to the resulting environment. -/
@[step]
theorem metadata.decode_env_section.profile_spec (data : Slice U8) (pos : Usize) (id : U8)
    (env : metadata.Env) (before : Declarations) (hb : Bounded env pos.val) :
    metadata.decode_env_section data pos id env ⦃ r => match r.1 with
      | .Ok next => ∃ after, Effect data pos env before id next r.2 after ∧ Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_env_section
  split
  · apply WP.spec_mono (metadata.decode_type_section.profile_spec data pos env hb.types)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs⟩ := hp
      refine ⟨_, .types hadd hbytes (by intro ft hm; exact (Profile.funcTypeAdmissible_iff ft).mpr (hv ft hm)), ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_import_section.spec data pos env hb)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hbound⟩ := hp
      refine ⟨_, .imports hadd hbytes, ?_⟩
      exact hbound
  · apply WP.spec_mono (metadata.decode_function_section.spec data pos env hb.funcs hb.funcIndices)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨indices, signatures, hadd, hbytes, hs, hi⟩ := hp
      refine ⟨_, .functions hadd hbytes, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_table_section.spec data pos env hb.tables)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs⟩ := hp
      refine ⟨_, .tables hadd hbytes hv, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_memory_section.spec data pos env hb.memories)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs, hc⟩ := hp
      refine ⟨_, .memories hadd hbytes hv hc, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_global_section.spec data pos env hb.globals hb.globalTypes hb.declaredFuncs)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs, ht, href⟩ := hp
      refine ⟨_, .globals hadd hbytes hv, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_export_section.spec data pos env hb)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hbound⟩ := hp
      refine ⟨_, .exports hadd hbytes, ?_⟩
      exact hbound
  · apply WP.spec_mono (metadata.decode_start_section.spec data pos env )
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨idx, hbytes, he, hi⟩ := hp
      refine ⟨_, .start he hbytes hi, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [he]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_element_section.profile_spec data pos env hb.elements hb.declaredFuncs)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨added, hadd, hbytes, hv, hs, href⟩ := hp
      refine ⟨_, .elements hadd hbytes hv, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [hadd.1]
      cases hold
      constructor <;> assumption
  · apply WP.spec_mono (metadata.decode_data_count.spec data pos env)
    rintro ⟨r, result⟩ hp
    cases r with
    | Err e => trivial
    | Ok next =>
      obtain ⟨count, hbytes, he⟩ := hp
      refine ⟨_, .dataCount he hbytes, ?_⟩
      have hold := hb.mono hbytes.span.1
      rw [he]
      cases hold
      constructor <;> assumption
  · simp

end Itasca

end

/-! ## Parser -/

section

/-!
# Environment parser soundness

Specifications of the environment parser `metadata.validate_env` and its helpers
`metadata.validate_env_with` and `metadata.validate_env_with_loop`. For arbitrary input they terminate,
and a successful result carries the ordered `Run` of sections that produced the environment.
`metadata.validate_env.profile_spec` is the main result, and the unsuffixed `.spec` theorems are its
Wasm 1.0 instances.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- Postcondition of the section loop for the module. An accepted result comes with a `Run` from the
initial state and a `Bounded` environment. -/
def LoopPostWith (data : Slice U8) (initial : metadata.Env) (decls : Declarations)
    (start : Usize) (initialId : U8) :
    core.result.Result (metadata.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ after last, Run data initial decls start initialId env after next last ∧
      Bounded env next.val

/-- Postcondition of `metadata.validate_env` for the module. An accepted result comes with a fresh
environment, the module header bytes, a `Run` of sections from the header to the returned
position, and a `Bounded` environment. -/
def PostWith (data : Slice U8) : core.result.Result (metadata.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ initial start decls last,
      metadata.Env.new = .ok initial ∧
      Wasm1.BytesAt data 0#usize ModuleBinary.magicVersion start ∧
      Run data initial {} start 0#u8 env decls next last ∧ Bounded env next.val

end Itasca.ModuleEnv

namespace Itasca

open ModuleBinary ModuleEnv

/-- The section loop either rejects or returns the ordered section history. Custom-section hooks
may reject, and they are only required to terminate. -/
theorem metadata.validate_env_with_loop.profile_spec {V : Type} (visitor : metadata.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (v : V)
    (env : metadata.Env) (decls : Declarations) (start : Usize) (initialId : U8)
    (hstart : start.val ≤ data.length) (hbound : Bounded env start.val) :
    metadata.validate_env_with_loop visitor data v env start initialId ⦃ r =>
      LoopPostWith data env decls start initialId r.1 ⦄ := by
  unfold metadata.validate_env_with_loop
  apply loop.spec_decr_nat (fun s => data.length - s.2.2.1.val)
    (fun s => ∃ currentDecls, Run data env decls start initialId s.2.1 currentDecls s.2.2.1 s.2.2.2 ∧
      Bounded s.2.1 s.2.2.1.val)
  · rintro ⟨state, current, pos, lastId⟩ ⟨currentDecls, hrun, hbound⟩
    dsimp only at hrun hbound
    have hpos := (hrun.span hstart).2
    unfold metadata.validate_env_with_loop.body
    dsimp only
    split
    · exact ⟨currentDecls, lastId, hrun, hbound⟩
    · rename_i hmore
      obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (metadata.read_section_header.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPostWith]
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        change SectionHeader data pos id first last at hh
        have hspan := hh.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        by_cases hc : id = metadata.SECTION_CUSTOM
        · simp only [hc, ↓reduceIte]
          obtain ⟨r, hcustom, hp⟩ := WP.spec_imp_exists (metadata.decode_custom_section.spec data first last)
          rw [hcustom]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPostWith]
          | Ok custom =>
            obtain ⟨nm, hn, hbefore, _, _⟩ := hp
            have hbytes := ModuleTail.custom_encoded (by simpa [hc, metadata.SECTION_CUSTOM] using hh) hn hbefore
            obtain ⟨⟨res, state'⟩, hvisit⟩ := htotal state custom
            simp [hvisit]
            cases res with
            | Err e => simp [LoopPostWith]
            | Ok u =>
              exact ⟨⟨currentDecls, .custom hrun hbytes⟩, hbound.mono (next := last.val) (by omega), by scalar_tac⟩
        · simp only [hc, ↓reduceIte]
          split
          · exact ⟨currentDecls, lastId, hrun, hbound⟩
          · split
            · exact ⟨currentDecls, lastId, hrun, hbound⟩
            · obtain ⟨rankResult, hrank, hrankPost⟩ := WP.spec_imp_exists (metadata.section_order.spec id)
              rw [hrank]
              cases rankResult with
              | Err e => simp [
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPostWith]
              | Ok rank =>
                obtain ⟨rfl, hidLow, hidHigh⟩ := hrankPost
                simp only [bind_ok]
                split
                · simp [LoopPostWith]
                · rename_i horder
                  have horder' : lastId.val < (sectionRank id).val := by scalar_tac
                  obtain ⟨⟨r, updated⟩, hread, hp⟩ := WP.spec_imp_exists
                    (metadata.decode_env_section.profile_spec data first id current currentDecls (hbound.mono (by omega)))
                  simp only [hread, bind_ok]
                  cases r with
                  | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPostWith]
                  | Ok next =>
                    obtain ⟨after, heffect, hbound⟩ := hp
                    simp
                    by_cases he : next = last
                    · subst next
                      simp only [↓reduceIte, WP.spec_ok]
                      exact ⟨⟨after, .step hrun horder' hh heffect⟩, hbound, by scalar_tac⟩
                    · have hn : next.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                      simp [hn, LoopPostWith]
  · exact ⟨decls, .nil, hbound⟩

/-- `metadata.validate_env_with` reads the header, starts from the empty environment and runs the
section loop, so its result satisfies `PostWith`. -/
theorem metadata.validate_env_with.profile_spec {V : Type} (visitor : metadata.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (v : V) :
    metadata.validate_env_with visitor data v ⦃ r => ModuleEnv.PostWith data r.1 ⦄ := by
  obtain ⟨initial, hi, _, _, hb⟩ := WP.spec_imp_exists metadata.Env.new.spec
  obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (metadata.read_header.spec data)
  cases r with
  | Err e => simp [metadata.validate_env_with, hi, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ModuleEnv.PostWith]
  | Ok start =>
    obtain ⟨⟨r, finalVisitor⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.validate_env_with_loop.profile_spec visitor htotal data v initial {} start 0#u8 hh.bound
        (hb.mono (Nat.zero_le _)))
    simp [metadata.validate_env_with, hi, hr, core.result.Result.Insts.CoreOpsTry.branch, hloop]
    cases r with
    | Err e => trivial
    | Ok pair =>
      obtain ⟨result, next⟩ := pair
      obtain ⟨decls, last, hrun, hbound⟩ := hp
      exact ⟨initial, start, decls, last, hi, hh, hrun, hbound⟩

/-- Arbitrary input bytes give an ordinary result from `metadata.validate_env`. A successful result
carries the complete ordered section history needed for declarative assembly. -/
theorem metadata.validate_env.profile_spec (data : Slice U8) :
    metadata.validate_env data ⦃ ModuleEnv.PostWith data ⦄ := by
  obtain ⟨⟨r, state⟩, hr, hp⟩ := WP.spec_imp_exists
    (metadata.validate_env_with.profile_spec metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      ModuleTail.empty_hooks_total data ())
  simpa [metadata.validate_env, hr] using hp

end Itasca

end

/-! ## NameFacts -/

section

/-!
# Name facts from the prefix grammar

Consequences of `PrefixEncoding` for import and export names: every member of an encoded vector has
its own byte encoding (`VecEncoding.member`), and import and export names are well-formed Unicode
names (`PrefixEncoding.import_names_wf`, `PrefixEncoding.export_names_wf`).
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- Every member of a related list has its own byte-format witness. -/
theorem Rep.member {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) {value} (hm : value ∈ values) : ∃ bs, R value bs := by
  induction h with
  | nil => simp at hm
  | cons hv _ ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, hv⟩
      · exact ih hm

theorem VecEncoding.member {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) {value} (hm : value ∈ values) : ∃ bs, R value bs := by
  obtain ⟨_, _, _, hr, _⟩ := h
  exact hr.member hm

theorem PaddedEncoding.member {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (h : PaddedEncoding id (VecEncoding R) [] values bytes)
    {value} (hm : value ∈ values) : ∃ bs, R value bs := by
  obtain ⟨_, _, _, hs, _⟩ := h
  cases hs with
  | absent => simp at hm
  | present hp =>
      obtain ⟨_, _, _, hr, _⟩ := hp
      exact hr.member hm

theorem ImportEncoding.names_wf {entry bytes} (h : ImportEncoding entry bytes) :
    wf_name (nameOfBytes entry.moduleName) ∧ wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, _, hmodule, hname, _, _⟩ := h
  exact ⟨hmodule.wellFormed, hname.wellFormed⟩

theorem ExportEncoding.name_wf {entry bytes} (h : ExportEncoding entry bytes) :
    wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, hname, _, _⟩ := h
  exact hname.wellFormed

end Itasca.ModuleBinary

namespace Itasca.ModuleEnv

open ModuleBinary

/-- Import module and field names in an encoded prefix are well-formed Unicode names. -/
theorem PrefixEncoding.import_names_wf {decls bytes} (h : PrefixEncoding decls bytes) :
    ∀ entry ∈ decls.imports,
      wf_name (nameOfBytes entry.moduleName) ∧ wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hi, _⟩ := h
  intro entry hm
  obtain ⟨bs, he⟩ := hi.member hm
  exact he.names_wf

/-- Export names in an encoded prefix are well-formed Unicode names. -/
theorem PrefixEncoding.export_names_wf {decls bytes} (h : PrefixEncoding decls bytes) :
    ∀ entry ∈ decls.exports, wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _⟩ := h
  intro entry hm
  obtain ⟨bs, hx⟩ := he.member hm
  exact hx.name_wf

end Itasca.ModuleEnv

end

/-! ## Encoding -/

section

/-!
# Byte layout of accepted environments

`Run.encoding` shows that every successful run of the section loop consumes exactly a
`PrefixEncoding` of the resulting declarations. The proof tracks a `Layout`, which assigns the bytes
read so far to the declaration slots, and extends it section by section with `Effect.append_layout`
and `Run.append_layout`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary

/-- Byte chunks for each declaration slot. Custom sections are attached to the slot that follows
them, and `customs` holds those not yet attached. Slots after the last section seen are empty. -/
structure Layout where
  types : List U8 := []
  imports : List U8 := []
  functions : List U8 := []
  tables : List U8 := []
  memories : List U8 := []
  globals : List U8 := []
  exports : List U8 := []
  start : List U8 := []
  elements : List U8 := []
  dataCount : List U8 := []
  customs : List U8 := []

/-- The concatenation of all chunks in section order. -/
def Layout.bytes (l : Layout) : List U8 :=
  l.types ++ l.imports ++ l.functions ++ l.tables ++ l.memories ++ l.globals ++ l.exports ++ l.start ++ l.elements ++ l.dataCount ++ l.customs

/-- Slots ranked after `last` have no bytes. -/
def Layout.Future (last : Nat) (l : Layout) : Prop :=
  (last < 1 → l.types = []) ∧
  (last < 2 → l.imports = []) ∧
  (last < 3 → l.functions = []) ∧
  (last < 4 → l.tables = []) ∧
  (last < 5 → l.memories = []) ∧
  (last < 6 → l.globals = []) ∧
  (last < 7 → l.exports = []) ∧
  (last < 8 → l.start = []) ∧
  (last < 9 → l.elements = []) ∧
  (last < 10 → l.dataCount = [])

/-- Each chunk of `l` is the canonical padded encoding of the matching slot of `decls`, the
trailing customs are well formed, and slots after `last` are empty. -/
structure Layout.Valid (last : Nat) (decls : Declarations) (l : Layout) : Prop where
  types : PaddedEncoding 1#u8 (VecEncoding FuncTypeEncoding) [] decls.types l.types
  imports : PaddedEncoding 2#u8 (VecEncoding ImportEncoding) [] decls.imports l.imports
  functions : PaddedEncoding 3#u8 (VecEncoding IndexEncoding) [] decls.functions l.functions
  tables : PaddedEncoding 4#u8 (VecEncoding TableTypeEncoding) [] decls.tables l.tables
  memories : PaddedEncoding 5#u8 (VecEncoding MemTypeEncoding) [] decls.memories l.memories
  globals : PaddedEncoding 6#u8 (VecEncoding GlobalEncoding) [] decls.globals l.globals
  exports : PaddedEncoding 7#u8 (VecEncoding ExportEncoding) [] decls.exports l.exports
  start : PaddedEncoding 8#u8 StartEncoding none decls.start l.start
  elements : PaddedEncoding 9#u8 (VecEncoding (ElementEncodingFor)) [] decls.elements l.elements
  dataCount : DataCountSectionEncoding decls.dataCount l.dataCount
  customs : CustomsEncoding l.customs
  future : l.Future last

/-- The empty layout encodes the empty declarations. -/
theorem Layout.valid_empty :
    Layout.Valid 0 ({} : Declarations) ({} : Layout) := by
  constructor
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact .nil
  · simp [global_simps, Layout.Future]

theorem Layout.Valid.custom {last decls l bytes} (h : Layout.Valid last decls l)
    (hc : CustomEncoding bytes) :
    Layout.Valid last decls {l with customs := l.customs ++ bytes} := by
  exact ⟨h.types, h.imports, h.functions, h.tables, h.memories, h.globals,
    h.exports, h.start, h.elements, h.dataCount,
    by simpa using ModuleTail.customs_append h.customs (.cons hc .nil), h.future⟩

/-- A section effect extends a valid layout, whose bytes end at the section header, to a valid
layout ending at the end of the section. -/
theorem Effect.append_layout {data origin pos first next env result before after id last l}
    (h : Effect data first env before id next result after)
    (hh : SectionHeader data pos id first next)
    (hl : Layout.Valid last before l) (ho : last < (sectionRank id).val)
    (hs : Wasm1.BytesAt data origin l.bytes pos) :
    ∃ updated, Layout.Valid (sectionRank id).val after updated ∧ Wasm1.BytesAt data origin updated.bytes next := by
  rcases hl.future with ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩
  cases h with
  | types hadd hb hv =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 1 at ho
    have hz1 : l.types = [] := hf1 (by omega)
    have hz2 : l.imports = [] := hf2 (by omega)
    have hz3 : l.functions = [] := hf3 (by omega)
    have hz4 : l.tables = [] := hf4 (by omega)
    have hz5 : l.memories = [] := hf5 (by omega)
    have hz6 : l.globals = [] := hf6 (by omega)
    have hz7 : l.exports = [] := hf7 (by omega)
    have hz8 : l.start = [] := hf8 (by omega)
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with types := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10]
  | imports hadd hb =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 2 at ho
    have hz2 : l.imports = [] := hf2 (by omega)
    have hz3 : l.functions = [] := hf3 (by omega)
    have hz4 : l.tables = [] := hf4 (by omega)
    have hz5 : l.memories = [] := hf5 (by omega)
    have hz6 : l.globals = [] := hf6 (by omega)
    have hz7 : l.exports = [] := hf7 (by omega)
    have hz8 : l.start = [] := hf8 (by omega)
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with imports := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, List.append_assoc]
  | functions hadd hb =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 3 at ho
    have hz3 : l.functions = [] := hf3 (by omega)
    have hz4 : l.tables = [] := hf4 (by omega)
    have hz5 : l.memories = [] := hf5 (by omega)
    have hz6 : l.globals = [] := hf6 (by omega)
    have hz7 : l.exports = [] := hf7 (by omega)
    have hz8 : l.start = [] := hf8 (by omega)
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with functions := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz4, hz5, hz6, hz7, hz8, hz9, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, List.append_assoc]
  | tables hadd hb hv =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 4 at ho
    have hz4 : l.tables = [] := hf4 (by omega)
    have hz5 : l.memories = [] := hf5 (by omega)
    have hz6 : l.globals = [] := hf6 (by omega)
    have hz7 : l.exports = [] := hf7 (by omega)
    have hz8 : l.start = [] := hf8 (by omega)
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with tables := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz5, hz6, hz7, hz8, hz9, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz4, hz5, hz6, hz7, hz8, hz9, hz10, List.append_assoc]
  | memories hadd hb hv hc =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 5 at ho
    have hz5 : l.memories = [] := hf5 (by omega)
    have hz6 : l.globals = [] := hf6 (by omega)
    have hz7 : l.exports = [] := hf7 (by omega)
    have hz8 : l.start = [] := hf8 (by omega)
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with memories := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz6, hz7, hz8, hz9, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz5, hz6, hz7, hz8, hz9, hz10, List.append_assoc]
  | globals hadd hb hv =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 6 at ho
    have hz6 : l.globals = [] := hf6 (by omega)
    have hz7 : l.exports = [] := hf7 (by omega)
    have hz8 : l.start = [] := hf8 (by omega)
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with globals := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz7, hz8, hz9, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz6, hz7, hz8, hz9, hz10, List.append_assoc]
  | exports hadd hb =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 7 at ho
    have hz7 : l.exports = [] := hf7 (by omega)
    have hz8 : l.start = [] := hf8 (by omega)
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with exports := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.start
      · exact hl.elements
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz8, hz9, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz7, hz8, hz9, hz10, List.append_assoc]
  | start he hb hi =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 8 at ho
    have hz8 : l.start = [] := hf8 (by omega)
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with start := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.elements
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz9, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz8, hz9, hz10, List.append_assoc]
  | elements hadd hb hv =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 9 at ho
    have hz9 : l.elements = [] := hf9 (by omega)
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with elements := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.dataCount
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future, hz10]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz9, hz10, List.append_assoc]
  | dataCount hstate hb =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    change last < 10 at ho
    have hz10 : l.dataCount = [] := hf10 (by omega)
    refine ⟨{ l with dataCount := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact .nil
      · simp [sectionRank, global_simps, Layout.Future]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz10, List.append_assoc]

/-- A run of the section loop extends a valid layout to a valid layout of the final declarations
that ends where the run ends. -/
theorem Run.append_layout {data initial decls start initialId after afterDecls next id origin l}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hl : Layout.Valid initialId.val decls l)
    (hs : Wasm1.BytesAt data origin l.bytes start) :
    ∃ updated, Layout.Valid id.val afterDecls updated ∧ Wasm1.BytesAt data origin updated.bytes next := by
  induction h with
  | nil => exact ⟨l, hl, hs⟩
  | custom _ hc ih =>
    obtain ⟨current, hv, hb⟩ := ih
    obtain ⟨bytes, he, hs⟩ := hc
    exact ⟨{ current with customs := current.customs ++ bytes }, hv.custom he,
      by simpa only [Layout.bytes, List.append_assoc] using hb.append hs⟩
  | step _ ho hh he ih =>
    obtain ⟨current, hv, hb⟩ := ih
    exact he.append_layout hh hv ho hb

/-- A valid layout is a `PrefixEncoding` of its declarations after the module header. -/
theorem Layout.Valid.encoding {last decls l} (h : Layout.Valid last decls l) :
    PrefixEncoding decls (magicVersion ++ l.bytes) := by
  exact ⟨l.types, l.imports, l.functions, l.tables, l.memories, l.globals, l.exports,
    l.start, l.elements, l.dataCount, l.customs, h.types, h.imports, h.functions, h.tables,
    h.memories, h.globals, h.exports, h.start, h.elements, h.dataCount, h.customs,
    by simp only [Layout.bytes, List.append_assoc]⟩

/-- A run from the end of the module header consumes exactly the independent encoding of the
resulting declarations. -/
theorem Run.encoding {data initial start after decls next id}
    (h : Run data initial {} start 0#u8 after decls next id)
    (hh : Wasm1.BytesAt data 0#usize magicVersion start) :
    At (fun decls bytes => PrefixEncoding decls bytes) data 0#usize decls next := by
  obtain ⟨layout, hv, hb⟩ := h.append_layout (Layout.valid_empty)
    (show Wasm1.BytesAt data start (Layout.bytes {}) start from Wasm1.BytesAt.nil data start hh.bound)
  exact ⟨magicVersion ++ layout.bytes, hv.encoding, hh.append hb⟩

end Itasca.ModuleEnv

end
