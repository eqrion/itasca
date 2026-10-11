import Itasca.Examples.ModuleExamples
import Itasca.Module.ModuleCompleteness
import Itasca.Examples.StreamSliceExamplesSupport

open Aeneas Aeneas.Std

namespace Itasca.ModuleSectionExamples

open ModuleBinary ModuleEnv

private theorem leb (b : U8) (h : b.val < 128 := by decide) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

private theorem one {α : Type} {R : α → List U8 → Prop} {x bs}
    (h : R x bs) : VecEncoding R [x] (1#u8 :: bs) :=
  ⟨[1#u8], bs, leb 1#u8, by simpa using Rep.cons h Rep.nil, rfl⟩

private theorem padded {α : Type} {R : α → List U8 → Prop} (id size : U8)
    (absent : α) {x bs} (h : R x bs) (hlen : bs.length = size.val)
    (hsize : size.val < 128 := by decide) :
    PaddedEncoding id R absent x (id :: size :: bs) :=
  ⟨[], _, .nil, .present ⟨[size], bs, hlen ▸ leb size hsize, h, rfl⟩, rfl⟩

private theorem omitted {α : Type} (id : U8) (R : α → List U8 → Prop) (absent : α) :
    PaddedEncoding id R absent absent [] := ⟨[], [], .nil, .absent, rfl⟩

def tableType : types.TableType := ⟨⟨0#u32, none⟩, .FuncRef⟩
def memoryType : types.MemType := ⟨⟨0#u32, none⟩⟩
def global : module.Global := ⟨⟨.Const, .I32⟩, .I32 0#i32⟩
def globalExport : ModuleBinary.Export := ⟨[0x67#u8], .Global 0#u32⟩
def element : ModuleBinary.Element := ⟨0#u32, .I32 0#i32, []⟩
def segment : module.Data := ⟨0#u32, .I32 0#i32, alloc.vec.Vec.from [42#u8] (by simp; scalar_tac)⟩

def declarations : Declarations :=
  { tables := [tableType], memories := [memoryType], globals := [global],
    exports := [globalExport], elements := [element] }

def raw : ModuleBinary.Module := declarations.module [] [ModuleData.raw segment]

def layout : Layout :=
  { tables := [4#u8,4#u8,1#u8,0x70#u8,0#u8,0#u8]
    memories := [5#u8,3#u8,1#u8,0#u8,0#u8]
    globals := [6#u8,6#u8,1#u8,0x7F#u8,0#u8,0x41#u8,0#u8,0x0B#u8]
    exports := [7#u8,5#u8,1#u8,1#u8,0x67#u8,3#u8,0#u8]
    elements := [9#u8,6#u8,1#u8,0#u8,0x41#u8,0#u8,0x0B#u8,0#u8] }

def dataBytes : List U8 := [11#u8,7#u8,1#u8,0#u8,0x41#u8,0#u8,0x0B#u8,1#u8,42#u8]
def input : Slice U8 := ModuleExamples.bytes (magicVersion ++ layout.bytes ++ dataBytes)
  (by simp [magicVersion, layout, Layout.bytes, dataBytes]; scalar_tac)

private theorem zero_const : ConstEncoding (.I32 0#i32) [0x41#u8,0#u8,0x0B#u8] :=
  .i32 _ ⟨[], 0#u8, rfl, by simp, by simp, by decide, rfl, by decide, by decide⟩

private theorem layout_valid : Layout.Valid 9 declarations layout := by
  constructor
  · exact omitted _ _ _
  · exact omitted _ _ _
  · exact omitted _ _ _
  · exact padded _ 4#u8 _ (one ⟨[0#u8,0#u8], .noMax _ (leb 0#u8), rfl⟩) rfl
  · exact padded _ 3#u8 _ (one (.noMax _ (leb 0#u8))) rfl
  · exact padded _ 6#u8 _ (one ⟨[0x7F#u8,0#u8], [0x41#u8,0#u8,0x0B#u8], rfl, zero_const, rfl⟩) rfl
  · exact padded _ 5#u8 _ (one ⟨[1#u8,0x67#u8], [3#u8,0#u8],
      ⟨ByteVecEncoding.iff.mpr ⟨[1#u8], leb 1#u8, rfl⟩,
        .cons (.one _ (by decide)) .nil⟩, .global _ (leb 0#u8), rfl⟩) rfl
  · exact omitted _ _ _
  · exact padded _ 6#u8 _ (one ⟨[0#u8], [0x41#u8,0#u8,0x0B#u8], [0#u8],
      leb 0#u8, zero_const, ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩, rfl⟩) rfl
  · exact .nil
  · simp [Layout.Future]

private theorem requirements : Requirements raw := by
  intro id decls env hlo hhi hr
  interval_cases id
  · simp [SectionValid, raw, declarations, Declarations.module]
  · refine ⟨?_, ?_, ?_⟩
    · simp [raw, declarations, Declarations.module]
    · simp [hr.empty_tables (by decide), ModuleSections.rawTables, raw, declarations, Declarations.module]
    · simp [hr.empty_memories (by decide), ModuleSections.rawMemories, raw, declarations, Declarations.module]
  · simp [SectionValid, raw, declarations, Declarations.module]
  · constructor
    · simp [raw, declarations, Declarations.module, tableType, LimitsValid, limits.MAX_TABLE_ELEMS]
    · rw [hr.tables_count (by decide) (by decide)]
      simp [raw, declarations, Declarations.module, ModuleTranslation.tables]
  · constructor
    · simp [raw, declarations, Declarations.module, memoryType, LimitsValid, limits.MAX_MEMORY_PAGES]
    · rw [hr.memories_count (by decide) (by decide)]
      simp [raw, declarations, Declarations.module, ModuleTranslation.mems]
  · intro g hg
    have hg : g = global := by simpa [raw, declarations, Declarations.module] using hg
    subst g
    exact .i32 _
  · constructor
    · simp [raw, declarations, Declarations.module]
    · intro e he
      have heq : e = globalExport := by simpa [raw, declarations, Declarations.module] using he
      subst e
      have hlen := congrArg List.length (hr.globals_context (by decide))
      simp [ModuleElaboration.contextOf, raw, declarations, Declarations.module,
        ModuleTranslation.globals] at hlen
      change 0 < env.global_types.val.length
      omega
  · simp [SectionValid, raw, declarations, Declarations.module]
  · intro e he
    have heq : e = element := by simpa [raw, declarations, Declarations.module] using he
    subst e
    refine ⟨?_, by exact .i32 _, by simp [element]⟩
    have hlen := congrArg List.length (hr.tables_context (by decide))
    simp [ModuleElaboration.contextOf, raw, declarations, Declarations.module,
      ModuleTranslation.tables] at hlen
    change 0 < env.table_types.val.length
    omega

private theorem data_encoding : SectionEncoding 11#u8 (VecEncoding DataEncoding)
    [ModuleData.raw segment] dataBytes := by
  refine ⟨[7#u8], [1#u8,0#u8,0x41#u8,0#u8,0x0B#u8,1#u8,42#u8], leb 7#u8, ?_, rfl⟩
  exact one ⟨[0#u8], [0x41#u8,0#u8,0x0B#u8], [1#u8,42#u8],
    leb 0#u8, zero_const, ByteVecEncoding.iff.mpr ⟨[1#u8], leb 1#u8, rfl⟩, rfl⟩

/-- A real 51-byte module exercises ordered sections, immutable initialization,
a named global export, and both kinds of active segment. -/
theorem sections_accepted : ∃ decoded, module.validate_module input = .ok (.Ok decoded) := by
  have hp : At PrefixEncoding input 0#usize declarations 42#usize := by
    refine ⟨magicVersion ++ layout.bytes, layout_valid.encoding, ?_⟩
    constructor <;> simp [input, ModuleExamples.bytes, alloc.vec.Vec.deref,
      magicVersion, layout, Layout.bytes, dataBytes]
  have hd : At (SectionEncoding 11#u8 (VecEncoding DataEncoding)) input 42#usize
      [ModuleData.raw segment] 51#usize := by
    refine ⟨dataBytes, data_encoding, ?_⟩
    constructor <;> simp [input, ModuleExamples.bytes, alloc.vec.Vec.deref,
      magicVersion, layout, Layout.bytes, dataBytes]
  obtain ⟨first, hh, _⟩ := hd.section_split
  let tail : module.Tail := ⟨alloc.vec.Vec.from [segment] (by simp; scalar_tac)⟩
  have ht : At ModuleTail.Encoding input 42#usize (tail.data.val.map ModuleData.raw) (Slice.len input) := by
    refine ⟨dataBytes, ⟨dataBytes, [], ⟨[], dataBytes, .nil, .present data_encoding, rfl⟩, .nil, rfl⟩, ?_⟩
    constructor <;> simp [input, ModuleExamples.bytes, alloc.vec.Vec.deref,
      magicVersion, layout, Layout.bytes, dataBytes]
  have hl : ModuleLayout.Layout input raw declarations 42#usize 42#usize :=
    ⟨rfl, hp, .inr ⟨rfl, rfl, .inr ⟨11#u8, first, 51#usize, hh, by decide⟩⟩,
      by simpa [tail, raw, declarations, Declarations.module] using ht,
      .inr ⟨11#u8, first, 51#usize, hh, by decide⟩⟩
  obtain ⟨env, ha⟩ := StreamSliceExamplesSupport.accepted_layout input raw declarations
    42#usize 42#usize hl (by
      simp [input, ModuleExamples.bytes, alloc.vec.Vec.deref,
        magicVersion, layout, Layout.bytes, dataBytes, limits.MAX_MODULE_BYTES])
    requirements tail rfl (by
      intro decls env hr
      rw [hr.functions_eq (by decide)]
      exact .nil) (by
      intro decls env hr s hs
      have heq : s = segment := by simpa [tail] using hs
      subst s
      refine ⟨?_, .i32 _⟩
      have hlen := congrArg List.length (hr.memories_context (by decide))
      simp [ModuleElaboration.contextOf, raw, declarations, Declarations.module,
        ModuleTranslation.mems] at hlen
      change 0 < env.mem_types.val.length
      omega)
  exact ⟨⟨env, tail⟩, ha⟩

/-- The certificate refers to the exact fixture bytes and includes generated
module typing, the Wasm 1.0 profile, and ordered external metadata. -/
theorem sections_validated : ∃ decoded, module.validate_module input = .ok (.Ok decoded) ∧
    ModuleSound.Validated input decoded := by
  obtain ⟨decoded, ha⟩ := sections_accepted
  exact ⟨decoded, ha, module.validate_module.wasm_sound _ _ ha⟩

end Itasca.ModuleSectionExamples
