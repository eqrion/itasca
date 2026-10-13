import Itasca.Module.Env.Requirements

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
def Payload (raw : ModuleBinary.Module) (id : Nat) (_ : Unit) (bytes : List U8)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  match id with
  | 1 => ModuleBinary.VecEncoding ModuleBinary.FuncTypeEncoding raw.types bytes
  | 2 => ModuleBinary.VecEncoding ModuleBinary.ImportEncoding raw.imports bytes
  | 3 => ModuleBinary.VecEncoding ModuleBinary.IndexEncoding raw.functions bytes
  | 4 => ModuleBinary.VecEncoding ModuleBinary.TableTypeEncoding raw.tables bytes
  | 5 => ModuleBinary.VecEncoding ModuleBinary.MemTypeEncoding raw.memories bytes
  | 6 => ModuleBinary.VecEncoding ModuleBinary.GlobalEncoding raw.globals bytes
  | 7 => ModuleBinary.VecEncoding ModuleBinary.ExportEncoding raw.exports bytes
  | 8 => ModuleBinary.StartEncoding raw.start bytes
  | 9 => ModuleBinary.VecEncoding (ModuleBinary.ElementEncodingFor profile) raw.elements bytes
  | 10 => profile = .Wasm2 ∧ ModuleBinary.StartEncoding raw.dataCount bytes
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
def SlotEncoding (raw : ModuleBinary.Module) (id : U8) (bytes : List U8)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  ∃ customs body, ModuleBinary.CustomsEncoding customs ∧
    ((Empty raw (ModuleBinary.sectionRank id).val ∧ body = []) ∨
      ModuleBinary.SectionEncoding id (fun u bytes => Payload raw (ModuleBinary.sectionRank id).val u bytes profile) () body) ∧
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
