import Itasca.Module.Env.Requirements
import Itasca.Module.Elab.SectionInversion
import Itasca.Module.Env.Encoding
import Itasca.Module.Sections.DeclarationsComplete
import Itasca.Module.Readers.Completeness

open WebAssembly

/-!
# Complete

Independent declarations construct ready environment contexts and successful section dispatch. Slot bounds, phase chaining and replay compose into environment completeness.
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

namespace Itasca.Module.Environment

/-- The payload encoding of the declaration section with rank `id` of `raw`. -/
def Payload (raw : Binary.Module) (id : Nat) (_ : Unit) (bytes : List U8) : Prop :=
  match id with
  | 1 => Binary.VecEncoding Binary.FuncTypeEncoding raw.types bytes
  | 2 => Binary.VecEncoding Binary.ImportEncoding raw.imports bytes
  | 3 => Binary.VecEncoding Binary.IndexEncoding raw.functions bytes
  | 4 => Binary.VecEncoding Binary.TableTypeEncoding raw.tables bytes
  | 5 => Binary.VecEncoding Binary.MemTypeEncoding raw.memories bytes
  | 6 => Binary.VecEncoding Binary.GlobalEncoding raw.globals bytes
  | 7 => Binary.VecEncoding Binary.ExportEncoding raw.exports bytes
  | 8 => Binary.StartEncoding raw.start bytes
  | 9 => Binary.VecEncoding Binary.ElementEncoding raw.elements bytes
  | 10 => Binary.StartEncoding raw.dataCount bytes
  | _ => False

/-- The slot of rank `id` is empty in `raw`, so the section may be omitted. -/
def Empty (raw : Binary.Module) (id : Nat) : Prop :=
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
def update (raw : Binary.Module) (id : Nat) (decls : Declarations) : Declarations :=
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
def SlotEncoding (raw : Binary.Module) (id : U8) (bytes : List U8) : Prop :=
  ∃ customs body, Binary.CustomsEncoding customs ∧
    ((Empty raw (Binary.sectionRank id).val ∧ body = []) ∨
      Binary.SectionEncoding id (fun u bytes => Payload raw (Binary.sectionRank id).val u bytes) () body) ∧
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

end Itasca.Module.Environment

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

namespace Itasca.Module.Environment

open Itasca.Binary

/-- The ten ordered optional declaration slots, followed by all custom bytes consumed before the
first code or data section. -/
inductive Chain (raw : Binary.Module) :
    Nat → List U8 → Prop where
  | done {bytes} : CustomsEncoding bytes → Chain raw 10 bytes
  | step {n : Nat} {id : U8} {first rest : List U8} :
      n < 10 → (sectionRank id).val = n + 1 → SlotEncoding raw id first → Chain raw (n + 1) rest →
      Chain raw n (first ++ rest)

/-- A padded section encoding is a slot encoding when the absent value is an empty slot and
every present payload is a valid payload for that section. -/
theorem padded_slot {α : Type} {R : α → List U8 → Prop} {raw : Binary.Module}
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
    (h : PrefixEncoding decls bytes) (codes : List Binary.Code) (datas : List Binary.Data) :
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

end Itasca.Module.Environment

end

/-! ## ReadyContexts -/

section

/-!
# Typing contexts of ready environments

Consequences of `Ready` for the environment `env` and the raw module `raw`. Once a section has been
processed, the environment's fields equal the raw module's, and the elaborated typing contexts
(`contextOf raw`) agree with the translated caches of `env`. `Ready.module_context` gives the
code-entry module context, and `Ready.matches` shows a fully ready environment matches the returned
metadata of the raw module.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

open Module.Elaboration

theorem Ready.types_eq {raw last decls env} (h : Ready raw last decls env) (hn : 1 ≤ last) :
    env.code.types.val = raw.types := h.represents.types.symm.trans (h.types hn)

theorem Ready.functions_eq {raw last decls env} (h : Ready raw last decls env) (hn : 3 ≤ last) :
    Translation.Environment.definedTypeIndices env.code = raw.functions :=
  h.represents.cache.defined_type_indices.trans (h.functions hn)

theorem Ready.elements_eq {raw last decls env} (h : Ready raw last decls env) (hn : 9 ≤ last) :
    env.elements.val.map rawElement = raw.elements := h.represents.elements.symm.trans (h.elements hn)

theorem Ready.data_count_eq {raw last decls env} (h : Ready raw last decls env) (hn : 10 ≤ last) :
    env.code.data_count = raw.dataCount := h.represents.dataCount.symm.trans (h.dataCount hn)

theorem Ready.elements_context {raw last decls env} (h : Ready raw last decls env) (hn : 9 ≤ last) :
    (contextOf raw).ELEMS = Translation.Environment.elementTypes env.code := by
  simp only [contextOf]
  simp [Translation.Environment.elementTypes, h.represents.elementTypes, h.elements hn, List.map_map, Function.comp_def]

/-- An encoded data count identifies the final data space. When it is omitted, the binary condition
rules out every data-index instruction in each body. -/
theorem Ready.data_context {raw last decls env} (h : Ready raw last decls env) (hn : 10 ≤ last)
    (hv : Binary.DataCountValid raw) (entry : Binary.Code) (hm : entry ∈ raw.codes) :
    (contextOf raw).DATAS = Translation.Environment.dataTypes env.code ∨ Binary.instructionsUseData entry.body = false := by
  cases hc : raw.dataCount with
  | none =>
    right
    exact (show ∀ code ∈ raw.codes, Binary.instructionsUseData code.body = false from by
      simpa only [Binary.DataCountValid, WebAssembly.Binary.DataCountValidWith, hc] using hv) entry hm
  | some count =>
    left
    have he : count.val = raw.data.length := by simpa only [Binary.DataCountValid, WebAssembly.Binary.DataCountValidWith, hc] using hv
    simp [contextOf, Translation.Environment.dataTypes, h.data_count_eq hn, hc, he]

theorem Ready.import_types_eq {raw last decls env} (h : Ready raw last decls env) (hn : 2 ≤ last) :
    importTypes env.code.types.val decls.imports = raw.imports.map (fun e => importType raw.types e.desc) := by
  simp [importTypes, h.types_eq (by omega), h.imports hn]

theorem Ready.funcs_context {raw last decls env} (h : Ready raw last decls env) (hn : 3 ≤ last) :
    (contextOf raw).FUNCS = env.code.funcs.val.map (Translation.Environment.descriptorType env.code.types.val) := by
  symm
  simpa [contextOf, importTypes, h.imports (by omega), h.functions hn, h.types_eq (by omega)] using funcs_cache h.represents.cache

theorem Ready.tables_context {raw last decls env} (h : Ready raw last decls env) (hn : 4 ≤ last) :
    (contextOf raw).TABLES = env.code.tables.val.map (fun d => Translation.Environment.tableType d.ty) := by
  symm
  simpa [contextOf, h.import_types_eq (by omega), h.tables hn] using tables_cache h.represents.cache

theorem Ready.memories_context {raw last decls env} (h : Ready raw last decls env) (hn : 5 ≤ last) :
    (contextOf raw).MEMS = env.code.memories.val.map (fun d => Translation.Environment.memType d.ty) := by
  symm
  simpa [contextOf, h.import_types_eq (by omega), h.memories hn] using memories_cache h.represents.cache

theorem Ready.globals_context {raw last decls env} (h : Ready raw last decls env) (hn : 6 ≤ last) :
    (contextOf raw).GLOBALS = env.code.globals.val.map (fun d => Translation.globalType d.gtype) := by
  symm
  simpa [contextOf, h.import_types_eq (by omega), h.globals hn] using globals_cache h.represents.cache

/-- Once the global section is processed, the environment is a code-entry module context for the
elaborated typing context. -/
theorem Ready.module_context {raw last decls env} (h : Ready raw last decls env) (hn : 6 ≤ last) :
    CodeEntry.ModuleContext env.code (contextOf raw) :=
  ⟨by simp [contextOf, h.types_eq (by omega)], h.funcs_context (by omega),
    h.globals_context hn, h.tables_context (by omega), h.memories_context (by omega), rfl, rfl⟩

theorem Ready.initializer_globals {raw last decls env} (h : Ready raw last decls env) (hn : 2 ≤ last) :
    Module.Constants.GlobalContext env.code (initializerContextOf raw) := by
  change Module.Translation.globals (raw.imports.map (fun e => importType raw.types e.desc)) = _
  rw [← h.import_types_eq hn, importTypes, globals_imports, ← h.represents.cache.global_prefix]
  simp [List.map_map, Function.comp_def]

theorem Ready.empty_imports {raw last decls env} (h : Ready raw last decls env) (hn : last < 2) :
    env.imports.val = [] := by
  have hp := h.phase.2.1 hn
  simpa [hp] using h.represents.imports

theorem Ready.future_tables {raw last decls env} (h : Ready raw last decls env) (hn : last < 4) :
    decls.tables = [] := h.phase.2.2.2.1 hn

theorem Ready.future_memories {raw last decls env} (h : Ready raw last decls env) (hn : last < 5) :
    decls.memories = [] := h.phase.2.2.2.2.1 hn

theorem Ready.empty_memories {raw last decls env} (h : Ready raw last decls env) (hn : last < 2) :
    env.code.memories.val = [] := by
  simpa [h.phase.2.1 hn, h.future_memories (by omega), importedMems] using h.represents.cache.memoryEntries

theorem Ready.memories_count {raw last decls env} (h : Ready raw last decls env)
    (hlo : 2 ≤ last) (hhi : last < 5) :
    env.code.memories.val.length =
      (Module.Translation.mems (raw.imports.map (fun e => importType raw.types e.desc))).length := by
  rw [← h.import_types_eq hlo, importTypes, mems_imports, List.length_map]
  simpa [h.future_memories hhi] using congrArg List.length h.represents.cache.memoryEntries

end Itasca.Module.Environment

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

/-- A fully decoded declaration prefix and a tail with the raw data segments match every returned
field of the raw module, including the merged index spaces. -/
theorem Ready.fromEnv_eq {raw : Binary.Module} {decls : Declarations} {env}
    (h : Ready raw 10 decls env) {segments} (hs : segments.map Module.Data.raw = raw.data) :
    Module.Elaboration.fromEnv env decls raw.codes segments = raw := by
  rw [← Module.Elaboration.represents_module h.represents, hs]
  cases raw
  simp [Declarations.module, h.types (by decide), h.imports (by decide), h.functions (by decide),
    h.tables (by decide), h.memories (by decide), h.globals (by decide), h.exports (by decide),
    h.start (by decide), h.elements (by decide), h.dataCount (by decide)]

end Itasca.Module.Environment

end

/-! ## DispatchComplete -/

section

/-!
# Section dispatch completeness

`metadata.decode_env_section.complete` shows that `metadata.decode_env_section` accepts the
independent encoding of any declaration section whose contents are valid, and returns the
`Effect` that updates the declarations.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Itasca.Binary Module.Sections Module.Environment

/-- For an independently encoded section payload with valid contents, `metadata.decode_env_section`
returns success at the end of the payload together with the `Effect` of the matching slot update.
The premises do not assume any parser execution. -/
theorem metadata.decode_env_section.complete (data : Slice U8) (pos : Usize) (id : U8)
    (env : metadata.ModuleMetadata metadata.CodeMetadata) (decls : Declarations) (raw : Binary.Module) (next : Usize)
    (hlo : 1 ≤ (sectionRank id).val) (hhi : (sectionRank id).val ≤ 10)
    (hb : At (fun u bs => Payload raw (sectionRank id).val u bs) data pos () next)
    (hv : SectionValid raw (sectionRank id).val env.code) (hready : Ready raw ((sectionRank id).val - 1) decls env)
    (hbound : Bounded env pos.val) :
    ∃ result, metadata.decode_env_section data pos id env = .ok (.Ok next, result) ∧
      Effect data pos env decls id next result (update raw (sectionRank id).val decls) := by
  have hc := section_rank_prefix hlo hhi
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · have he : id = 1#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_type_section.complete data pos env.code raw.types next hb
      (by intro ft hm; exact hv ft hm) hbound.types
    exact ⟨{env with code := result}, by simp [metadata.decode_env_section, hr, global_simps],
      .types ha hb hv⟩
  · have he : id = 2#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ImportEncoding) data pos raw.imports next at hb
    obtain ⟨result, hr, ha⟩ := metadata.decode_import_section.complete data pos env raw.imports next hb hv hbound
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    exact .imports ha hb
  · have he : id = 3#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_function_section.complete data pos env.code raw.functions next hb hv hbound.funcs
    exact ⟨{env with code := result}, by simp [metadata.decode_env_section, hr, global_simps],
      .functions ha hb⟩
  · have he : id = 4#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_table_section.complete data pos env.code raw.tables next hb hv hbound.tables
    refine ⟨{env with code := result}, by simp [metadata.decode_env_section, hr, global_simps], .tables ha hb ?_⟩
    intro tt ht
    simpa [Module.Translation.LimitsValid, Binary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hv tt ht
  · have he : id = 5#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_memory_section.complete data pos env.code raw.memories next hb hv.1 hv.2
    refine ⟨{env with code := result}, by simp [metadata.decode_env_section, hr, global_simps], .memories ha hb ?_ ?_⟩
    · intro mt ht
      simpa [Module.Translation.LimitsValid, Binary.LimitsValid, Option.mem_def, global_simps] using hv.1 mt ht
    · have hc : result.memories.val.length ≤ 1 := by simpa only [ha.2, List.length_append, List.length_map] using hv.2
      exact hc.trans (Nat.le_max_right _ _)
  · have he : id = 6#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_global_section.complete data pos env.code raw.globals next hb hv hbound.globals
    refine ⟨{env with code := result}, by simp [metadata.decode_env_section, hr, global_simps], .globals ha hb ?_⟩
    intro g hg
    exact (hv g hg).append_globals _ ha.2.1 (by rw [ha.1]) (by simpa using congrArg List.length ha.2.2.funcs)
  · have he : id = 7#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ExportEncoding) data pos raw.exports next at hb
    have hempty : env.exports.val = [] := by
      have hx := hready.represents.exports.symm.trans (hready.phase.2.2.2.2.2.2.1 (by decide))
      exact List.map_eq_nil_iff.mp hx
    obtain ⟨result, actual, hr, ha, hraw⟩ := metadata.decode_export_section.complete data pos env raw.exports next hb hempty hv.1 hv.2
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    simpa [Payload, update, hraw, sectionRank, global_simps] using (Effect.exports (before := decls) ha (by simpa [Payload, update, hraw, sectionRank, global_simps] using hb))
  · have he : id = 8#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨bs, ⟨idx, hstart, hi⟩, hs⟩ := hb
    have hbytes : At StartEncoding data pos (some idx) next := ⟨bs, ⟨idx, rfl, hi⟩, hs⟩
    obtain ⟨ft, resolved, hp, hr⟩ := hv idx hstart
    obtain ⟨fd, lookup, signature, read⟩ :=
      metadata.decode_start_section.complete data pos env.code idx next hbytes resolved hp hr
    refine ⟨{env with code := {env.code with start := some idx, funcs := env.code.funcs.set (UScalar.cast .Usize idx) {fd with eager := true}}}, by simp [metadata.decode_env_section, read, global_simps], ?_⟩
    simpa [update, hstart, sectionRank, global_simps] using
      (Effect.start (env := env) (before := decls) rfl hbytes ⟨lookup, ft, signature, hp, hr⟩)
  · have he : id = 9#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ElementEncoding) data pos raw.elements next at hb
    obtain ⟨result, actual, hr, hraw, ha⟩ := metadata.decode_element_section.complete data pos env raw.elements next hb hv hbound.elements hbound.elementTypes
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    have hva : ∀ e ∈ actual, ElementValid env.code e := by
      intro e he
      have hm : Module.Environment.rawElement e ∈ raw.elements := by rw [← hraw]; exact List.mem_map.mpr ⟨e, he, rfl⟩
      exact hv _ hm
    simpa [Payload, update, hraw, sectionRank, global_simps] using (Effect.elements (before := decls) ha (by simpa [Payload, update, hraw, sectionRank, global_simps] using hb) hva)
  · have he : id = 12#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (fun (_ : Unit) bs => StartEncoding raw.dataCount bs) data pos () next at hb
    obtain ⟨bs, hstart, hspan⟩ := hb
    obtain ⟨idx, hcount, hindex⟩ := hstart
    have hbytes : At StartEncoding data pos (some idx) next := ⟨bs, ⟨idx, rfl, hindex⟩, hspan⟩
    have hread := metadata.decode_data_count.complete data pos env.code idx next hbytes
    refine ⟨{env with code := {env.code with data_count := some idx}}, by simp [metadata.decode_env_section, hread, global_simps], ?_⟩
    simpa [update, hcount, sectionRank] using (Effect.dataCount (before := decls) rfl hbytes)

end Itasca

end

/-! ## Replay -/

section

/-!
# Replaying the environment loop

Equations that unfold `metadata.validate_env_with_loop` with the empty module visitor, abbreviated
`Module.Environment.parseLoop`, one step at a time. Stopping at a code or data header
(`complete_stop`), skipping custom sections (`complete_custom`, `complete_customs`) and decoding
a declaration section (`complete_section`) are each stated as an equation on `parseLoop`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

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

end Itasca.Binary

namespace Itasca

open Itasca.Binary Module.Environment

/-- The environment section loop run with the empty module visitor. -/
abbrev Module.Environment.parseLoop (data : Slice U8) (env : metadata.ModuleMetadata metadata.CodeMetadata) (pos : Usize) (last : U8)
     :=
  metadata.validate_env_with_loop metadata.DefaultModuleVisitor.Insts.ItascaMetadataModuleVisitor
    data () env pos last

/-- At end of input or at a code or data header, the loop returns the current environment and
position. -/
theorem metadata.validate_env_with_loop.complete_stop (data : Slice U8) (env : metadata.ModuleMetadata metadata.CodeMetadata)
    (pos : Usize) (last : U8) (hstop : StopAt data pos) :
    Module.Environment.parseLoop data env pos last = .ok (.Ok (env, pos), ()) := by
  rcases hstop with rfl | ⟨id, first, next, hh, hid⟩
  · unfold Module.Environment.parseLoop metadata.validate_env_with_loop
    rw [Aeneas.Std.loop]
    simp [metadata.validate_env_with_loop.body]
  · have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
    have hr := metadata.read_section_header.complete data pos id first next hh
    unfold Module.Environment.parseLoop metadata.validate_env_with_loop
    rw [Aeneas.Std.loop]
    rcases hid with rfl | rfl <;>
      simp [metadata.validate_env_with_loop.body, hmore, hr, global_simps,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- The loop skips one custom section. -/
theorem metadata.validate_env_with_loop.complete_custom (data : Slice U8) (env : metadata.ModuleMetadata metadata.CodeMetadata)
    (pos next : Usize) (last : U8)
    (hb : At (fun (_ : Unit) => CustomEncoding) data pos () next) :
    Module.Environment.parseLoop data env pos last = Module.Environment.parseLoop data env next last := by
  obtain ⟨first, nameEnd, nm, hh, hn, hbefore⟩ := hb.custom_split
  have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hr := metadata.read_section_header.complete data pos 0#u8 first next hh
  obtain ⟨custom, hc, _⟩ := metadata.decode_custom_section.complete_raw data first nameEnd next nm hn hbefore
  unfold Module.Environment.parseLoop metadata.validate_env_with_loop
  conv_lhs => rw [Aeneas.Std.loop]
  simp [metadata.validate_env_with_loop.body, hmore, hr, hc, global_simps,
    metadata.ModuleVisitor.on_custom_section.default, core.result.Result.Insts.CoreOpsTry.branch]

/-- The loop skips any run of custom sections. -/
theorem metadata.validate_env_with_loop.complete_customs (data : Slice U8) (env : metadata.ModuleMetadata metadata.CodeMetadata)
    (pos next : Usize) (last : U8)
    (hb : At (fun (_ : Unit) => CustomsEncoding) data pos () next) :
    Module.Environment.parseLoop data env pos last = Module.Environment.parseLoop data env next last := by
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
    (env result : metadata.ModuleMetadata metadata.CodeMetadata) (pos first next : Usize) (last id : U8)
    (hh : SectionHeader data pos id first next)
    (hlo : 1 ≤ (sectionRank id).val) (hhi : (sectionRank id).val ≤ 10)
    (horder : last.val < (sectionRank id).val)
    (hread : metadata.decode_env_section data first id env = .ok (.Ok next, result)) :
    Module.Environment.parseLoop data env pos last = Module.Environment.parseLoop data result next (sectionRank id) := by
  have hid := section_rank_prefix hlo hhi
  have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hcustom : id ≠ metadata.SECTION_CUSTOM := by simp only [global_simps]; scalar_tac
  have hcode : id ≠ metadata.SECTION_CODE := by simp only [global_simps]; scalar_tac
  have hdata : id ≠ metadata.SECTION_DATA := by simp only [global_simps]; scalar_tac
  have hlast : ¬ (sectionRank id).val ≤ last.val := by omega
  have hrank := metadata.section_order.complete id (by omega) (by omega)
  have hr := metadata.read_section_header.complete data pos id first next hh
  unfold Module.Environment.parseLoop metadata.validate_env_with_loop
  conv_lhs => rw [Aeneas.Std.loop]
  simp [metadata.validate_env_with_loop.body, hmore, hr, hcustom, hcode, hdata, hlast,
    hrank, hread, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## Complete -/

section

/-!
# Completeness of the environment parser

`metadata.validate_env.complete` shows that an independently encoded declaration prefix
meeting the declarative requirements makes `metadata.validate_env` succeed at the greedy boundary
and reach a ready state. `Chain.complete` is the loop induction behind it.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

open Itasca.Binary

/-- The parser loop `parseLoop` accepts any `Chain` encoding. Absent slots advance the ghost
phase, and only actual sections update the parser's last-seen section id. -/
theorem Chain.complete {raw n bytes} (h : Chain raw n bytes)
    (data : Slice U8) (env : metadata.ModuleMetadata metadata.CodeMetadata) (decls : Declarations) (pos next : Usize) (last : U8)
    (hb : Body.Scalar.BytesAt data pos bytes next) (hstop : StopAt data next)
    (hready : Ready raw n decls env) (hbound : Bounded env pos.val)
    (indices : DescriptorIndices env.code) (hlast : last.val ≤ n) (hreq : Requirements raw) :
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
      obtain ⟨result, finalDecls, hrun, hr⟩ := ih env decls afterCustoms last hremaining hr hbound' indices (by omega)
      exact ⟨result, finalDecls, hcustomeq.trans hrun, hr⟩
    · obtain ⟨payloadStart, hh, hencoding⟩ := At.section_split
        (show At (SectionEncoding id (fun u bs => Payload raw (sectionRank id).val u bs)) data afterCustoms () middle from ⟨_, hpresent, hsection⟩)
      have hboundPayload := hbound'.mono (Nat.le_of_lt hh.span.1)
      obtain ⟨updated, hread, heffect⟩ := metadata.decode_env_section.complete data payloadStart id env decls raw middle
        hlo hhi hencoding (hreq (sectionRank id).val decls env hlo hhi hready') hready' hboundPayload
      have hrep := heffect.represents hready'.represents hready'.phase (by omega)
      have hr : Ready raw (n + 1) (update raw (sectionRank id).val decls) updated := by
        simpa only [hid] using hready'.updated hlo hhi hrep
      have hupdated : Bounded updated middle.val := by
        have hs := metadata.decode_env_section.spec data payloadStart id env decls hboundPayload indices
        simp only [hread, WP.spec_ok] at hs
        exact hs.choose_spec.2
      obtain ⟨result, finalDecls, hrun, hr⟩ := ih updated (update raw (sectionRank id).val decls) middle (sectionRank id) hremaining hr hupdated (heffect.indices indices) (by omega)
      refine ⟨result, finalDecls, hcustomeq.trans ?_, hr⟩
      exact (metadata.validate_env_with_loop.complete_section data env updated afterCustoms payloadStart middle last id
        hh hlo (by omega) (by omega) hread).trans hrun

end Itasca.Module.Environment

namespace Itasca

open Itasca.Binary Module.Environment

/-- Declarative requirements and an independently encoded complete environment
prefix imply success of the actual environment parser at its greedy boundary. -/
theorem metadata.validate_env.complete (data : Slice U8) (raw : Binary.Module)
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
  obtain ⟨initial, hnew, hrep, valid, _, hbound, hphase⟩ := WP.spec_imp_exists (metadata.ModuleMetadataCodeMetadata.new.declarations)
  have hready : Ready raw 0 {} initial := by
    refine ⟨hrep, hphase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨env, finalDecls, hrun, hready⟩ := hchain'.complete data initial {} start next 0#u8
    hsections hstop hready (hbound.mono (Nat.zero_le _)) valid.funcs (by simp) hrequirements
  refine ⟨env, finalDecls, ?_, hready⟩
  simp [metadata.validate_env, metadata.validate_env_with, hnew, hread,
    core.result.Result.Insts.CoreOpsTry.branch, hrun]

end Itasca

end
