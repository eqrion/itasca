import Itasca.Module.Env.Requirements
import Itasca.Module.Elab.SectionInversion
import Itasca.Module.Env.Encoding
import Itasca.Module.Sections.TypeComplete
import Itasca.Module.Sections.GlobalComplete
import Itasca.Module.Readers.TypesComplete

/-!
Sections, each formerly its own module: Slots, Chain, ReadyContexts, DispatchComplete, Replay, Complete.
-/

/-! ## Slots -/

section

/-!
# Declaration slots

Slot-level views of a raw module, indexed by section rank (`1` for types through `10` for data
count). `Payload` is the encoding of a section's payload, `Empty` says the slot is empty, `update`
fills the slot of a `Declarations` record from the raw module, and `SlotEncoding` is a slot's
bytes with its leading custom sections. `Ready.updated` and `Ready.absent` advance `Ready` over a
present or omitted section.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 800000

namespace Itasca.ModuleEnv

/-- The payload encoding of the declaration section with rank `id` of `raw`. -/
def Payload (raw : ModuleBinary.Module) (id : Nat) (_ : Unit) (bytes : List U8) : Prop :=
  match id with
  | 1 => ModuleBinary.VecEncoding ModuleBinary.FuncTypeEncoding raw.types bytes
  | 2 => ModuleBinary.VecEncoding ModuleBinary.ImportEncoding raw.imports bytes
  | 3 => ModuleBinary.VecEncoding ModuleBinary.IndexEncoding raw.functions bytes
  | 4 => ModuleBinary.VecEncoding ModuleBinary.TableTypeEncoding raw.tables bytes
  | 5 => ModuleBinary.VecEncoding ModuleBinary.MemTypeEncoding raw.memories bytes
  | 6 => ModuleBinary.VecEncoding ModuleBinary.GlobalEncoding raw.globals bytes
  | 7 => ModuleBinary.VecEncoding ModuleBinary.ExportEncoding raw.exports bytes
  | 8 => ModuleBinary.StartEncoding raw.start bytes
  | 9 => ModuleBinary.VecEncoding (ModuleBinary.ElementEncodingFor) raw.elements bytes
  | 10 => ModuleBinary.StartEncoding raw.dataCount bytes
  | _ => False

/-- The slot of rank `id` is empty in `raw`, so the section may be omitted. -/
def Empty (raw : ModuleBinary.Module) (id : Nat) : Prop :=
  match id with
  | 1 => raw.types = []
  | 2 => raw.imports = []
  | 3 => raw.functions = []
  | 4 => raw.tables = []
  | 5 => raw.memories = []
  | 6 => raw.globals = []
  | 7 => raw.exports = []
  | 8 => raw.start = none
  | 9 => raw.elements = []
  | 10 => raw.dataCount = none
  | _ => False

/-- `decls` with the slot of rank `id` replaced by the raw module's contents. -/
def update (raw : ModuleBinary.Module) (id : Nat) (decls : Declarations) : Declarations :=
  match id with
  | 1 => {decls with types := raw.types}
  | 2 => {decls with imports := raw.imports}
  | 3 => {decls with functions := raw.functions}
  | 4 => {decls with tables := raw.tables}
  | 5 => {decls with memories := raw.memories}
  | 6 => {decls with globals := raw.globals}
  | 7 => {decls with exports := raw.exports}
  | 8 => {decls with start := raw.start}
  | 9 => {decls with elements := raw.elements}
  | 10 => {decls with dataCount := raw.dataCount}
  | _ => decls

/-- The bytes of the slot with id `id`: leading custom sections followed by either a present section
or nothing when the slot is empty. An omitted empty section completes its slot just as a present
section does. -/
def SlotEncoding (raw : ModuleBinary.Module) (id : U8) (bytes : List U8) : Prop :=
  ∃ customs body, ModuleBinary.CustomsEncoding customs ∧
    ((Empty raw (ModuleBinary.sectionRank id).val ∧ body = []) ∨
      ModuleBinary.SectionEncoding id (fun u bytes => Payload raw (ModuleBinary.sectionRank id).val u bytes) () body) ∧
    bytes = customs ++ body

/-- Filling slot `id` of the declarations from the raw module advances `Ready` to `id`. -/
theorem Ready.updated {raw id decls env result} (h : Ready raw (id - 1) decls env)
    (hlo : 1 ≤ id) (hhi : id ≤ 10) (hr : Represents result (update raw id decls)) :
    Ready raw id (update raw id decls) result := by
  rcases h with ⟨_, hp, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hc : id = 1 ∨ id = 2 ∨ id = 3 ∨ id = 4 ∨ id = 5 ∨ id = 6 ∨ id = 7 ∨ id = 8 ∨ id = 9 ∨ id = 10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> simp_all [update, Phase]

theorem Ready.update_empty {raw id decls env} (h : Ready raw (id - 1) decls env)
    (hlo : 1 ≤ id) (hhi : id ≤ 10) (he : Empty raw id) : update raw id decls = decls := by
  rcases h with ⟨_, hp, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  rcases decls with ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount⟩
  have hc : id = 1 ∨ id = 2 ∨ id = 3 ∨ id = 4 ∨ id = 5 ∨ id = 6 ∨ id = 7 ∨ id = 8 ∨ id = 9 ∨ id = 10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [update, Empty, Phase]

/-- Omitting an empty section advances `Ready` to `id` without changing the declarations. -/
theorem Ready.absent {raw id decls env} (h : Ready raw (id - 1) decls env)
    (hlo : 1 ≤ id) (hhi : id ≤ 10) (he : Empty raw id) : Ready raw id decls env := by
  have heq := h.update_empty hlo hhi he
  simpa only [heq] using h.updated hlo hhi (by simpa only [heq] using h.represents)

end Itasca.ModuleEnv

end

/-! ## Chain -/

section

/-!
# Ordered section chain

`Chain` restates the independent prefix grammar as the ten ordered optional declaration slots
followed by trailing custom sections, indexed by how many slots have been passed.
`PrefixEncoding.chain` converts a `PrefixEncoding` into a `Chain` for the parser's run order.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary

/-- The ten ordered optional declaration slots, followed by all custom bytes consumed before the
first code or data section. -/
inductive Chain (raw : ModuleBinary.Module) :
    Nat → List U8 → Prop where
  | done {bytes} : CustomsEncoding bytes → Chain raw 10 bytes
  | step {n : Nat} {id : U8} {first rest : List U8} :
      n < 10 → (sectionRank id).val = n + 1 → SlotEncoding raw id first → Chain raw (n + 1) rest →
      Chain raw n (first ++ rest)

/-- A padded section encoding is a slot encoding when the absent value is an empty slot and
every present payload is a valid payload for that section. -/
theorem padded_slot {α : Type} {R : α → List U8 → Prop} {raw : ModuleBinary.Module}
    {id : U8} {value absent : α} {bytes : List U8}
    (h : PaddedEncoding id R absent value bytes)
    (hzero : value = absent → Empty raw (sectionRank id).val)
    (hpayload : ∀ bs, R value bs → Payload raw (sectionRank id).val () bs) : SlotEncoding raw id bytes := by
  obtain ⟨customs, body, hc, hs, rfl⟩ := h
  refine ⟨customs, body, hc, ?_, rfl⟩
  cases hs with
  | absent => exact .inl ⟨hzero rfl, rfl⟩
  | present hsection =>
    obtain ⟨size, payload, hsize, hp, rfl⟩ := hsection
    exact .inr ⟨size, payload, hsize, hpayload payload hp, rfl⟩

/-- A `PrefixEncoding` after the module header is a `Chain` starting at slot `0`, keeping all
custom-section bytes and all empty slots. -/
theorem PrefixEncoding.chain {decls : Declarations} {bytes : List U8}
    (h : PrefixEncoding decls bytes) (codes : List ModuleBinary.Code) (datas : List ModuleBinary.Data) :
    ∃ suffix, Chain (decls.module codes datas) 0 suffix ∧ bytes = magicVersion ++ suffix := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    customs, ht, hi, hf, hta, hm, hg, he, hs, hel, hdc, hc, rfl⟩ := h
  have ht' := padded_slot (raw := decls.module codes datas) ht (fun h => h) (fun _ h => h)
  have hi' := padded_slot (raw := decls.module codes datas) hi (fun h => h) (fun _ h => h)
  have hf' := padded_slot (raw := decls.module codes datas) hf (fun h => h) (fun _ h => h)
  have hta' := padded_slot (raw := decls.module codes datas) hta (fun h => h) (fun _ h => h)
  have hm' := padded_slot (raw := decls.module codes datas) hm (fun h => h) (fun _ h => h)
  have hg' := padded_slot (raw := decls.module codes datas) hg (fun h => h) (fun _ h => h)
  have he' := padded_slot (raw := decls.module codes datas) he (fun h => h) (fun _ h => h)
  have hs' := padded_slot (raw := decls.module codes datas) hs (fun h => h) (fun _ h => h)
  have hel' := padded_slot (raw := decls.module codes datas) hel (fun h => h) (fun _ h => h)
  have hdc' : SlotEncoding (decls.module codes datas) 12#u8 dataCount := by
    exact padded_slot hdc (fun h => h) (fun _ h => h)
  refine ⟨types ++ imports ++ functions ++ tables ++ memories ++ globals ++ exports ++ start ++ elements ++ dataCount ++ customs,
    ?_, by simp [List.append_assoc]⟩
  simpa only [List.append_assoc] using
    (Chain.step (n := 0) (id := 1#u8) (by decide) rfl ht'
    (Chain.step (n := 1) (id := 2#u8) (by decide) rfl hi'
    (Chain.step (n := 2) (id := 3#u8) (by decide) rfl hf'
    (Chain.step (n := 3) (id := 4#u8) (by decide) rfl hta'
    (Chain.step (n := 4) (id := 5#u8) (by decide) rfl hm'
    (Chain.step (n := 5) (id := 6#u8) (by decide) rfl hg'
    (Chain.step (n := 6) (id := 7#u8) (by decide) rfl he'
    (Chain.step (n := 7) (id := 8#u8) (by decide) rfl hs'
    (Chain.step (n := 8) (id := 9#u8) (by decide) rfl hel'
    (Chain.step (n := 9) (id := 12#u8) (by decide) rfl hdc' (.done hc)))))))))))

end Itasca.ModuleEnv

end

/-! ## ReadyContexts -/

section

/-!
# Typing contexts of ready environments

Consequences of `Ready` for the environment `env` and the raw module `raw`. Once a section has been
processed, the environment's fields equal the raw module's, and the elaborated typing contexts
(`contextOf raw`) agree with the translated caches of `env`. `Ready.moduleContext` gives the
code-entry module context, and `Ready.matches` shows a fully ready environment matches the returned
metadata of the raw module.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleElaboration

theorem Ready.types_eq {raw last decls env} (h : Ready raw last decls env) (hn : 1 ≤ last) :
    env.types.val = raw.types := h.represents.types.symm.trans (h.types hn)

theorem Ready.imports_eq {raw last decls env} (h : Ready raw last decls env) (hn : 2 ≤ last) :
    env.imports.val.map rawImport = raw.imports := h.represents.imports.symm.trans (h.imports hn)

theorem Ready.functions_eq {raw last decls env} (h : Ready raw last decls env) (hn : 3 ≤ last) :
    env.func_type_indices.val = raw.functions := h.represents.functions.symm.trans (h.functions hn)

theorem Ready.globals_eq {raw last decls env} (h : Ready raw last decls env) (hn : 6 ≤ last) :
    env.globals.val = raw.globals := h.represents.globals.symm.trans (h.globals hn)

theorem Ready.elements_eq {raw last decls env} (h : Ready raw last decls env) (hn : 9 ≤ last) :
    env.elements.val.map rawElement = raw.elements := h.represents.elements.symm.trans (h.elements hn)

theorem Ready.dataCount_eq {raw last decls env} (h : Ready raw last decls env) (hn : 10 ≤ last) :
    env.data_count = raw.dataCount := h.represents.dataCount.symm.trans (h.dataCount hn)

theorem Ready.elements_context {raw last decls env} (h : Ready raw last decls env) (hn : 9 ≤ last) :
    (contextOf raw).ELEMS = EnvTranslation.elementTypes env := by
  simp only [contextOf]
  rw [← h.elements_eq hn]
  simp [EnvTranslation.elementTypes, rawElement, List.map_map]

/-- An encoded data count identifies the final data space. When it is omitted, the binary condition
rules out every data-index instruction in each body. -/
theorem Ready.data_context {raw last decls env} (h : Ready raw last decls env) (hn : 10 ≤ last)
    (hv : ModuleBinary.DataCountValid raw) (entry : ModuleBinary.Code) (hm : entry ∈ raw.codes) :
    (contextOf raw).DATAS = EnvTranslation.dataTypes env ∨ ModuleBinary.instructionsUseData entry.body = false := by
  cases hc : raw.dataCount with
  | none =>
    right
    exact (show ∀ code ∈ raw.codes, ModuleBinary.instructionsUseData code.body = false from by
      simpa only [ModuleBinary.DataCountValid, hc] using hv) entry hm
  | some count =>
    left
    have he : count.val = raw.data.length := by simpa only [ModuleBinary.DataCountValid, hc] using hv
    simp [contextOf, EnvTranslation.dataTypes, h.dataCount_eq hn, hc, he]

theorem Ready.importTypes_eq {raw last decls env} (h : Ready raw last decls env) (hn : 2 ≤ last) :
    importTypes env = raw.imports.map (fun e => importType raw.types e.desc) := by
  rw [← h.imports_eq hn]
  simp [importTypes, h.types_eq (by omega), List.map_map, rawImport, Function.comp_def]

theorem Ready.funcs_context {raw last decls env} (h : Ready raw last decls env) (hn : 3 ≤ last) :
    (contextOf raw).FUNCS = env.func_types.val.map EnvTranslation.funcType := by
  symm
  simpa [contextOf, h.importTypes_eq (by omega), h.functions_eq hn, h.types_eq (by omega)] using funcs_cache h.represents.cache

theorem Ready.tables_context {raw last decls env} (h : Ready raw last decls env) (hn : 4 ≤ last) :
    (contextOf raw).TABLES = env.table_types.val.map EnvTranslation.tableType := by
  symm
  simpa [contextOf, h.importTypes_eq (by omega), h.tables hn] using tables_cache h.represents.cache

theorem Ready.memories_context {raw last decls env} (h : Ready raw last decls env) (hn : 5 ≤ last) :
    (contextOf raw).MEMS = env.mem_types.val.map EnvTranslation.memType := by
  symm
  simpa [contextOf, h.importTypes_eq (by omega), h.memories hn] using memories_cache h.represents.cache

theorem Ready.globals_context {raw last decls env} (h : Ready raw last decls env) (hn : 6 ≤ last) :
    (contextOf raw).GLOBALS = env.global_types.val.map Translate.globalType := by
  symm
  simpa [contextOf, h.importTypes_eq (by omega), h.globals_eq hn] using globals_cache h.represents.cache

/-- Once the global section is processed, the environment is a code-entry module context for the
elaborated typing context. -/
theorem Ready.moduleContext {raw last decls env} (h : Ready raw last decls env) (hn : 6 ≤ last) :
    CodeEntry.ModuleContext env (contextOf raw) :=
  ⟨by simp [contextOf, h.types_eq (by omega)], h.funcs_context (by omega),
    h.globals_context hn, h.tables_context (by omega), h.memories_context (by omega), rfl, rfl⟩

theorem Ready.initializer_globals {raw last decls env} (h : Ready raw last decls env) (hn : 2 ≤ last) :
    ModuleConstants.GlobalContext env (initializerContextOf raw) := by
  change ModuleTranslation.globals (raw.imports.map (fun e => importType raw.types e.desc)) = _
  rw [← h.importTypes_eq hn, importTypes, globals_imports, h.represents.cache.global_prefix]

theorem Ready.empty_imports {raw last decls env} (h : Ready raw last decls env) (hn : last < 2) :
    env.imports.val = [] := by
  have hp := h.phase.2.1 hn
  exact List.map_eq_nil_iff.mp (h.represents.imports.symm.trans hp)

theorem Ready.future_tables {raw last decls env} (h : Ready raw last decls env) (hn : last < 4) :
    decls.tables = [] := h.phase.2.2.2.1 hn

theorem Ready.future_memories {raw last decls env} (h : Ready raw last decls env) (hn : last < 5) :
    decls.memories = [] := h.phase.2.2.2.2.1 hn

theorem Ready.empty_tables {raw last decls env} (h : Ready raw last decls env) (hn : last < 2) :
    env.table_types.val = [] := by
  simp [h.represents.cache.tables, h.empty_imports hn, h.future_tables (by omega), importedTables]

theorem Ready.empty_memories {raw last decls env} (h : Ready raw last decls env) (hn : last < 2) :
    env.mem_types.val = [] := by
  simp [h.represents.cache.memories, h.empty_imports hn, h.future_memories (by omega), importedMems]

theorem Ready.tables_count {raw last decls env} (h : Ready raw last decls env)
    (hlo : 2 ≤ last) (hhi : last < 4) :
    env.table_types.val.length =
      (ModuleTranslation.tables (raw.imports.map (fun e => importType raw.types e.desc))).length := by
  rw [← h.importTypes_eq hlo, importTypes, tables_imports, List.length_map,
    h.represents.cache.tables, h.future_tables hhi, List.append_nil]

theorem Ready.memories_count {raw last decls env} (h : Ready raw last decls env)
    (hlo : 2 ≤ last) (hhi : last < 5) :
    env.mem_types.val.length =
      (ModuleTranslation.mems (raw.imports.map (fun e => importType raw.types e.desc))).length := by
  rw [← h.importTypes_eq hlo, importTypes, mems_imports, List.length_map,
    h.represents.cache.memories, h.future_memories hhi, List.append_nil]

end Itasca.ModuleEnv

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- A fully decoded declaration prefix and a tail with the raw data segments match every returned
field of the raw module, including the merged index spaces. -/
theorem Ready.matches {raw : ModuleBinary.Module} {decls : Declarations} {env : metadata.Env}
    (h : Ready raw 10 decls env) (tail : metadata.Tail)
    (htail : tail.data.val.map ModuleData.raw = raw.data) :
    ModuleElaboration.Matches env tail raw := by
  have hr := h.represents
  have ht := h.types (by decide)
  have hi := h.imports (by decide)
  have hf := h.functions (by decide)
  have hta := h.tables (by decide)
  have hm := h.memories (by decide)
  have hg := h.globals (by decide)
  have he := h.exports (by decide)
  have hs := h.start (by decide)
  have hel := h.elements (by decide)
  have hdc := h.dataCount (by decide)
  refine ⟨?_, by simpa [hta, hm] using hr.cache⟩
  cases raw
  simp_all [ModuleElaboration.fromEnv, hr.types, hr.imports, hr.functions, hr.globals,
      hr.exports, hr.start, hr.elements, hr.dataCount]

end Itasca.ModuleEnv

end

/-! ## DispatchComplete -/

section

/-!
# Section dispatch completeness

`metadata.decode_env_section.profile_complete` shows that `metadata.decode_env_section` accepts the
independent encoding of any declaration section whose contents are valid, and returns the
`Effect` that updates the declarations.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections ModuleEnv

/-- For an independently encoded section payload with valid contents, `metadata.decode_env_section`
returns success at the end of the payload together with the `Effect` of the matching slot update.
The premises do not assume any parser execution. -/
theorem metadata.decode_env_section.profile_complete (data : Slice U8) (pos : Usize) (id : U8)
    (env : metadata.Env) (decls : Declarations) (raw : ModuleBinary.Module) (next : Usize)
    (hlo : 1 ≤ (sectionRank id).val) (hhi : (sectionRank id).val ≤ 10)
    (hb : At (fun u bs => Payload raw (sectionRank id).val u bs) data pos () next)
    (hv : SectionValid raw (sectionRank id).val env) (hready : Ready raw ((sectionRank id).val - 1) decls env)
    (hbound : Bounded env pos.val) :
    ∃ result, metadata.decode_env_section data pos id env = .ok (.Ok next, result) ∧
      Effect data pos env decls id next result (update raw (sectionRank id).val decls) := by
  have hc := sectionRank_prefix hlo hhi
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · have he : id = 1#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_type_section.profile_complete data pos env raw.types next hb
      (by intro ft hm; exact (Profile.funcTypeAdmissible_iff ft).mp (hv ft hm)) hbound.types
    exact ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr,
      .types ha hb hv⟩
  · have he : id = 2#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ImportEncoding) data pos raw.imports next at hb
    obtain ⟨result, actual, hr, hraw, ha⟩ := metadata.decode_import_section.complete data pos env raw.imports next hb hv hbound
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    simpa [Payload, update, hraw, sectionRank, global_simps] using (Effect.imports (before := decls) ha (by simpa [Payload, update, hraw, sectionRank, global_simps] using hb))
  · have he : id = 3#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, sigs, hr, ha⟩ := metadata.decode_function_section.complete data pos env raw.functions next hb hv hbound.funcs hbound.funcIndices
    exact ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr,
      .functions ha hb⟩
  · have he : id = 4#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_table_section.complete data pos env raw.tables next hb hv hbound.tables
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, .tables ha hb ?_⟩
    intro tt ht
    simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hv tt ht
  · have he : id = 5#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_memory_section.complete data pos env raw.memories next hb hv.1 hv.2
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, .memories ha hb ?_ ?_⟩
    · intro mt ht
      simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps] using hv.1 mt ht
    · have hc : result.mem_types.val.length ≤ 1 := by simpa only [ha.2, List.length_append] using hv.2
      exact hc.trans (Nat.le_max_right _ _)
  · have he : id = 6#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_global_section.complete data pos env raw.globals next hb hv hbound.globals hbound.globalTypes hbound.declaredFuncs
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, .globals ha hb ?_⟩
    intro g hg
    exact (hv g hg).append_globals _ ha.2.2.1 (by rw [ha.1]) (by rw [ha.1])
  · have he : id = 7#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ExportEncoding) data pos raw.exports next at hb
    have hempty : env.exports.val = [] := by
      have hx := hready.represents.exports.symm.trans (hready.phase.2.2.2.2.2.2.1 (by decide))
      exact List.map_eq_nil_iff.mp hx
    obtain ⟨result, actual, hr, ha, hraw⟩ := metadata.decode_export_section.complete data pos env raw.exports next hb hempty hv.1 hv.2 hbound.declaredFuncs
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    simpa [Payload, update, hraw, sectionRank, global_simps] using (Effect.exports (before := decls) ha (by simpa [Payload, update, hraw, sectionRank, global_simps] using hb))
  · have he : id = 8#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨bs, ⟨idx, hstart, hi⟩, hs⟩ := hb
    have hbytes : At StartEncoding data pos (some idx) next := ⟨bs, ⟨idx, rfl, hi⟩, hs⟩
    obtain ⟨hidx, hp, hr⟩ := hv idx hstart
    have hread := metadata.decode_start_section.complete data pos env idx next hbytes hidx hp hr
    refine ⟨{env with start := some idx}, by simpa [metadata.decode_env_section, global_simps] using hread, ?_⟩
    simpa [update, hstart, sectionRank, global_simps] using (Effect.start (before := decls) rfl hbytes ⟨hidx, hp, hr⟩)
  · have he : id = 9#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding (ElementEncodingFor)) data pos raw.elements next at hb
    obtain ⟨result, actual, hr, hraw, ha⟩ := metadata.decode_element_section.profile_complete data pos env raw.elements next hb hv hbound.elements hbound.declaredFuncs
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    have hva : ∀ e ∈ actual, ElementValid env e := by
      intro e he
      have hm : ModuleEnv.rawElement e ∈ raw.elements := by rw [← hraw]; exact List.mem_map.mpr ⟨e, he, rfl⟩
      exact hv _ hm
    simpa [Payload, update, hraw, sectionRank, global_simps] using (Effect.elements (before := decls) ha (by simpa [Payload, update, hraw, sectionRank, global_simps] using hb) hva)
  · have he : id = 12#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (fun (_ : Unit) bs => StartEncoding raw.dataCount bs) data pos () next at hb
    obtain ⟨bs, hstart, hspan⟩ := hb
    obtain ⟨idx, hcount, hindex⟩ := hstart
    have hbytes : At StartEncoding data pos (some idx) next := ⟨bs, ⟨idx, rfl, hindex⟩, hspan⟩
    have hread := metadata.decode_data_count.complete data pos env idx next hbytes
    refine ⟨{env with data_count := some idx}, by simpa [metadata.decode_env_section, global_simps] using hread, ?_⟩
    simpa [update, hcount, sectionRank] using (Effect.dataCount (before := decls) rfl hbytes)

end Itasca

end

/-! ## Replay -/

section

/-!
# Replaying the environment loop

Equations that unfold `metadata.validate_env_with_loop` with the empty module visitor, abbreviated
`ModuleEnv.parseLoop`, one step at a time. Stopping at a code or data header
(`complete_stop`), skipping custom sections (`complete_custom`, `complete_customs`) and decoding
a declaration section (`complete_section`) are each stated as an equation on `parseLoop`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A custom section encoding has a section header and a name span inside it. The remaining payload
bytes are uninterpreted. -/
theorem At.custom_split {data pos next} (h : At (fun (_ : Unit) => CustomEncoding) data pos () next) :
    ∃ first nameEnd nm, SectionHeader data pos 0#u8 first next ∧
      At NameEncoding data first nm nameEnd ∧ nameEnd.val ≤ next.val := by
  obtain ⟨bytes, ⟨nm, payload, nameBytes, hn, hs⟩, hb⟩ := h
  obtain ⟨first, hh, encoded, he, hpayload⟩ :=
    At.section_split (show At (SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = nameBytes ++ payload))
      data pos () next from ⟨bytes, hs, hb⟩)
  subst encoded
  obtain ⟨nameEnd, hname, hrest⟩ := hpayload.split
  exact ⟨first, nameEnd, nm, hh, ⟨nameBytes, hn, hname⟩, by have := hrest.length; omega⟩

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary ModuleEnv

/-- The environment section loop run with the empty module visitor. -/
abbrev ModuleEnv.parseLoop (data : Slice U8) (env : metadata.Env) (pos : Usize) (last : U8)
     :=
  metadata.validate_env_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
    data () env pos last

/-- At end of input or at a code or data header, the loop returns the current environment and
position. -/
theorem metadata.validate_env_with_loop.complete_stop (data : Slice U8) (env : metadata.Env)
    (pos : Usize) (last : U8) (hstop : StopAt data pos) :
    ModuleEnv.parseLoop data env pos last = .ok (.Ok (env, pos), ()) := by
  rcases hstop with rfl | ⟨id, first, next, hh, hid⟩
  · unfold ModuleEnv.parseLoop metadata.validate_env_with_loop
    rw [Aeneas.Std.loop]
    simp [metadata.validate_env_with_loop.body]
  · have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
    have hr := metadata.read_section_header.complete data pos id first next hh
    unfold ModuleEnv.parseLoop metadata.validate_env_with_loop
    rw [Aeneas.Std.loop]
    rcases hid with rfl | rfl <;>
      simp [metadata.validate_env_with_loop.body, hmore, hr, global_simps,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- The loop skips one custom section. -/
theorem metadata.validate_env_with_loop.complete_custom (data : Slice U8) (env : metadata.Env)
    (pos next : Usize) (last : U8)
    (hb : At (fun (_ : Unit) => CustomEncoding) data pos () next) :
    ModuleEnv.parseLoop data env pos last = ModuleEnv.parseLoop data env next last := by
  obtain ⟨first, nameEnd, nm, hh, hn, hbefore⟩ := hb.custom_split
  have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hr := metadata.read_section_header.complete data pos 0#u8 first next hh
  obtain ⟨custom, hc, _⟩ := metadata.decode_custom_section.complete_raw data first nameEnd next nm hn hbefore
  unfold ModuleEnv.parseLoop metadata.validate_env_with_loop
  conv_lhs => rw [Aeneas.Std.loop]
  simp [metadata.validate_env_with_loop.body, hmore, hr, hc, global_simps,
    metadata.ModuleVisitor.on_custom_section.default, core.result.Result.Insts.CoreOpsTry.branch]

/-- The loop skips any run of custom sections. -/
theorem metadata.validate_env_with_loop.complete_customs (data : Slice U8) (env : metadata.Env)
    (pos next : Usize) (last : U8)
    (hb : At (fun (_ : Unit) => CustomsEncoding) data pos () next) :
    ModuleEnv.parseLoop data env pos last = ModuleEnv.parseLoop data env next last := by
  obtain ⟨bytes, hc, hs⟩ := hb
  induction hc generalizing pos with
  | nil => rw [hs.empty]
  | cons hcustom hrest ih =>
    obtain ⟨middle, hfirst, hremaining⟩ := hs.split
    rw [metadata.validate_env_with_loop.complete_custom data env pos middle last ⟨_, hcustom, hfirst⟩ ]
    exact ih middle hremaining

/-- When `metadata.decode_env_section` succeeds on a declaration section in increasing order, the
loop continues from the end of the section with the updated environment and last-seen rank. -/
theorem metadata.validate_env_with_loop.complete_section (data : Slice U8)
    (env result : metadata.Env) (pos first next : Usize) (last id : U8)
    (hh : SectionHeader data pos id first next)
    (hlo : 1 ≤ (sectionRank id).val) (hhi : (sectionRank id).val ≤ 10)
    (horder : last.val < (sectionRank id).val)
    (hread : metadata.decode_env_section data first id env = .ok (.Ok next, result)) :
    ModuleEnv.parseLoop data env pos last = ModuleEnv.parseLoop data result next (sectionRank id) := by
  have hid := sectionRank_prefix hlo hhi
  have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hcustom : id ≠ metadata.SECTION_CUSTOM := by simp only [global_simps]; scalar_tac
  have hcode : id ≠ metadata.SECTION_CODE := by simp only [global_simps]; scalar_tac
  have hdata : id ≠ metadata.SECTION_DATA := by simp only [global_simps]; scalar_tac
  have hlast : ¬ (sectionRank id).val ≤ last.val := by omega
  have hrank := metadata.section_order.complete id (by omega) (by omega)
  have hr := metadata.read_section_header.complete data pos id first next hh
  unfold ModuleEnv.parseLoop metadata.validate_env_with_loop
  conv_lhs => rw [Aeneas.Std.loop]
  simp [metadata.validate_env_with_loop.body, hmore, hr, hcustom, hcode, hdata, hlast,
    hrank, hread, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## Complete -/

section

/-!
# Completeness of the environment parser

`metadata.validate_env.profile_complete` shows that an independently encoded declaration prefix
meeting the declarative requirements makes `metadata.validate_env` succeed at the greedy boundary
and reach a ready state. `Chain.profile_complete` is the loop induction behind it.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary

/-- The parser loop `parseLoop` accepts any `Chain` encoding. Absent slots advance the ghost
phase, and only actual sections update the parser's last-seen section id. -/
theorem Chain.profile_complete {raw n bytes} (h : Chain raw n bytes)
    (data : Slice U8) (env : metadata.Env) (decls : Declarations) (pos next : Usize) (last : U8)
    (hb : Wasm1.BytesAt data pos bytes next) (hstop : StopAt data next)
    (hready : Ready raw n decls env) (hbound : Bounded env pos.val)
    (hlast : last.val ≤ n) (hreq : Requirements raw) :
    ∃ result finalDecls, parseLoop data env pos last = .ok (.Ok (result, next), ()) ∧
      Ready raw 10 finalDecls result := by
  induction h generalizing env decls pos last with
  | @done bytes hc =>
    refine ⟨env, decls, ?_, hready⟩
    rw [metadata.validate_env_with_loop.complete_customs data env pos next last ⟨_, hc, hb⟩ ]
    exact metadata.validate_env_with_loop.complete_stop data env next last hstop
  | @step n id first rest hn hid hslot hrest ih =>
    obtain ⟨middle, hfirst, hremaining⟩ := hb.split
    obtain ⟨customs, body, hc, hbody, heq⟩ := hslot
    rw [heq] at hfirst
    obtain ⟨afterCustoms, hcustoms, hsection⟩ := hfirst.split
    have hcustomeq := metadata.validate_env_with_loop.complete_customs data env pos afterCustoms last ⟨_, hc, hcustoms⟩
    have hbound' : Bounded env afterCustoms.val := hbound.mono (by have := hcustoms.length; omega)
    have hlo : 1 ≤ (sectionRank id).val := by omega
    have hhi : (sectionRank id).val ≤ 10 := by omega
    have hready' : Ready raw ((sectionRank id).val - 1) decls env := by simpa only [hid, Nat.add_sub_cancel] using hready
    rcases hbody with ⟨hempty, rfl⟩ | hpresent
    · have hend := hsection.empty
      subst middle
      have hr : Ready raw (n + 1) decls env := by simpa only [hid] using hready'.absent hlo hhi hempty
      obtain ⟨result, finalDecls, hrun, hr⟩ := ih env decls afterCustoms last hremaining hr hbound' (by omega)
      exact ⟨result, finalDecls, hcustomeq.trans hrun, hr⟩
    · obtain ⟨payloadStart, hh, hencoding⟩ := At.section_split
        (show At (SectionEncoding id (fun u bs => Payload raw (sectionRank id).val u bs)) data afterCustoms () middle from ⟨_, hpresent, hsection⟩)
      have hboundPayload := hbound'.mono (Nat.le_of_lt hh.span.1)
      obtain ⟨updated, hread, heffect⟩ := metadata.decode_env_section.profile_complete data payloadStart id env decls raw middle
        hlo hhi hencoding (hreq (sectionRank id).val decls env hlo hhi hready') hready' hboundPayload
      have hrep := heffect.represents hready'.represents hready'.phase (by omega)
      have hr : Ready raw (n + 1) (update raw (sectionRank id).val decls) updated := by
        simpa only [hid] using hready'.updated hlo hhi hrep
      have hupdated : Bounded updated middle.val := by
        have hs := metadata.decode_env_section.profile_spec data payloadStart id env decls hboundPayload
        simp only [hread, WP.spec_ok] at hs
        exact hs.choose_spec.2
      obtain ⟨result, finalDecls, hrun, hr⟩ := ih updated (update raw (sectionRank id).val decls) middle (sectionRank id) hremaining hr hupdated (by omega)
      refine ⟨result, finalDecls, hcustomeq.trans ?_, hr⟩
      exact (metadata.validate_env_with_loop.complete_section data env updated afterCustoms payloadStart middle last id
        hh hlo (by omega) (by omega) hread).trans hrun

end Itasca.ModuleEnv

namespace Itasca

open ModuleBinary ModuleEnv

/-- Declarative requirements and an independently encoded complete environment
prefix imply success of the actual environment parser at its greedy boundary. -/
theorem metadata.validate_env.profile_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (decls : Declarations) (next : Usize)
    (hprefix : At (fun ds bs => PrefixEncoding ds bs) data 0#usize decls next)
    (hraw : raw = decls.module raw.codes raw.data)
    (hstop : StopAt data next) (hrequirements : Requirements raw) :
    ∃ env finalDecls, metadata.validate_env data = .ok (.Ok (env, next)) ∧
      Ready raw 10 finalDecls env := by
  obtain ⟨bytes, hp, hs⟩ := hprefix
  obtain ⟨suffix, hchain, hbytes⟩ := hp.chain raw.codes raw.data
  have hchain' : Chain raw 0 suffix := by simpa only [← hraw] using hchain
  rw [hbytes] at hs
  obtain ⟨start, hheader, hsections⟩ := hs.split
  have hread := metadata.read_header.complete data start hheader
  obtain ⟨initial, hnew, hrep, _, _, hbound, hphase⟩ := WP.spec_imp_exists (metadata.Env.new.profile_declarations)
  have hready : Ready raw 0 {} initial := by
    refine ⟨hrep, hphase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨env, finalDecls, hrun, hready⟩ := hchain'.profile_complete data initial {} start next 0#u8
    hsections hstop hready (hbound.mono (Nat.zero_le _)) (by simp) hrequirements
  refine ⟨env, finalDecls, ?_, hready⟩
  simp [metadata.validate_env, metadata.validate_env_with, hnew, hread,
    core.result.Result.Insts.CoreOpsTry.branch, hrun]

end Itasca

end
