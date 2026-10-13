import Itasca.Module.Env.Requirements

open Aeneas Aeneas.Std

set_option maxHeartbeats 800000

namespace Itasca.ModuleEnv

/-- The raw payload of each standard environment section. -/
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

/-- An omitted empty section completes its slot just as a present section does. -/
def SlotEncoding (raw : ModuleBinary.Module) (id : U8) (bytes : List U8)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  ∃ customs body, ModuleBinary.CustomsEncoding customs ∧
    ((Empty raw (ModuleBinary.sectionRank id).val ∧ body = []) ∨
      ModuleBinary.SectionEncoding id (fun u bytes => Payload raw (ModuleBinary.sectionRank id).val u bytes profile) () body) ∧
    bytes = customs ++ body

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

theorem Ready.absent {raw id decls env} (h : Ready raw (id - 1) decls env)
    (hlo : 1 ≤ id) (hhi : id ≤ 10) (he : Empty raw id) : Ready raw id decls env := by
  have heq := h.update_empty hlo hhi he
  simpa only [heq] using h.updated hlo hhi (by simpa only [heq] using h.represents)

end Itasca.ModuleEnv
