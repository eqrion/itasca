import Itasca.Binary.Wasm1.Encoding

/-!
Sections, each formerly its own module: Module, PrefixUnique, Unicode, UnicodeUnique.
-/

/-! ## Module -/

section

/-!
# Module binary grammar

The handwritten, relational binary format of whole Wasm 2.0 modules. It defines raw
module syntax (`ModuleBinary.Module`) and the byte-level relations for LEB-prefixed vectors,
names, types, constant expressions, imports, exports, element and data segments, code entries
and sections. `ModuleEncodingWith` assembles them into the module grammar and `ModuleEncoding`
instantiates it with `CodeEncoding`. The grammar states syntax only: typing and implementation
limits are separate premises.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- Raw module syntax keeps indices as written and locals in their binary groups. Names are bytes;
their Unicode validity is a separate judgment (`NameEncoding`). -/
structure Import where
  moduleName : List U8
  «name» : List U8
  desc : metadata.ImportDesc

/-- A raw export: a byte-string name and its descriptor. -/
structure Export where
  «name» : List U8
  desc : metadata.ExportDesc

/-- A raw element segment: element type, mode and initializer expressions. -/
structure Element where
  elem : wasm_types.ElemType
  mode : metadata.ElementMode
  init : List wasm_types.ConstExpr

/-- A raw code entry: grouped local declarations and the structured body. -/
structure Code where
  locals : List (U32 × wasm_types.ValueType)
  body : List instr

/-- The flattened local types declared by a code entry. -/
def Code.declared (entry : Code) : List wasm_types.ValueType :=
  entry.locals.flatMap (fun (count, ty) => List.replicate count.val ty)

/-- A raw data segment: its mode and the initializer bytes. -/
structure Data where
  mode : metadata.DataMode
  init : List U8

/-- A raw module: the decoded contents of every section, before any typing check. -/
structure Module where
  types : List wasm_types.FuncType
  imports : List Import
  functions : List U32
  tables : List _root_.Itasca.wasm_types.TableType
  memories : List _root_.Itasca.wasm_types.MemType
  globals : List metadata.Global
  exports : List Export
  start : Option U32
  elements : List Element
  dataCount : Option U32
  codes : List Code
  data : List Data

/-- The encoding `R` of `value` occupies exactly the interval from `start` to `next` of `data`. -/
def At {α : Type} (R : α → List U8 → Prop) (data : Slice U8)
    (start : Usize) (value : α) (next : Usize) : Prop :=
  ∃ bytes, R value bytes ∧ Wasm1.BytesAt data start bytes next

/-- A list of values whose encodings, concatenated in order, form the byte list. -/
inductive Rep {α : Type} (R : α → List U8 → Prop) : List α → List U8 → Prop where
  | nil : Rep R [] []
  | cons {value values first rest} : R value first → Rep R values rest →
      Rep R (value :: values) (first ++ rest)

/-- A vector: a `u32` LEB128 count equal to the length, followed by the entries' encodings. -/
def VecEncoding {α : Type} (R : α → List U8 → Prop) (values : List α)
    (bytes : List U8) : Prop :=
  ∃ count entries, Leb128.Encoding count values.length ∧ Rep R values entries ∧
    bytes = count ++ entries

/-- An index as an unsigned LEB128 `u32`. -/
def IndexEncoding (index : U32) (bytes : List U8) : Prop :=
  Leb128.Encoding bytes index.val

/-- A single raw byte. -/
def ByteEncoding (byte : U8) (bytes : List U8) : Prop := bytes = [byte]

/-- A vector of raw bytes. -/
def ByteVecEncoding : List U8 → List U8 → Prop := VecEncoding ByteEncoding

/-- A Unicode scalar's shortest UTF-8 byte sequence. The bounds exclude
surrogates, overlong sequences, and scalar values above U+10FFFF. -/
inductive Utf8Char : List U8 → Prop where
  | one (a : U8) : a.val ≤ 0x7F → Utf8Char [a]
  | two (a b : U8) : 0xC2 ≤ a.val → a.val ≤ 0xDF →
      0x80 ≤ b.val → b.val ≤ 0xBF → Utf8Char [a, b]
  | three (a b c : U8) :
      ((a.val = 0xE0 ∧ 0xA0 ≤ b.val ∧ b.val ≤ 0xBF) ∨
       (0xE1 ≤ a.val ∧ a.val ≤ 0xEC ∧ 0x80 ≤ b.val ∧ b.val ≤ 0xBF) ∨
       (a.val = 0xED ∧ 0x80 ≤ b.val ∧ b.val ≤ 0x9F) ∨
       (0xEE ≤ a.val ∧ a.val ≤ 0xEF ∧ 0x80 ≤ b.val ∧ b.val ≤ 0xBF)) →
      0x80 ≤ c.val → c.val ≤ 0xBF → Utf8Char [a, b, c]
  | four (a b c d : U8) :
      ((a.val = 0xF0 ∧ 0x90 ≤ b.val ∧ b.val ≤ 0xBF) ∨
       (0xF1 ≤ a.val ∧ a.val ≤ 0xF3 ∧ 0x80 ≤ b.val ∧ b.val ≤ 0xBF) ∨
       (a.val = 0xF4 ∧ 0x80 ≤ b.val ∧ b.val ≤ 0x8F)) →
      0x80 ≤ c.val → c.val ≤ 0xBF → 0x80 ≤ d.val → d.val ≤ 0xBF →
      Utf8Char [a, b, c, d]

/-- A concatenation of `Utf8Char` sequences. -/
inductive Utf8 : List U8 → Prop where
  | nil : Utf8 []
  | cons {first rest} : Utf8Char first → Utf8 rest → Utf8 (first ++ rest)

/-- A name: a byte vector whose contents are valid UTF-8. -/
def NameEncoding (nm bytes : List U8) : Prop := ByteVecEncoding nm bytes ∧ Utf8 nm

/-- The binary type byte of a value type. -/
def valueByte : wasm_types.ValueType → U8
  | .I32 => 0x7F#u8 | .I64 => 0x7E#u8 | .F32 => 0x7D#u8 | .F64 => 0x7C#u8
  | .V128 => 0x7B#u8 | .FuncRef => 0x70#u8 | .ExternRef => 0x6F#u8

/-- The binary type byte of a reference element type. -/
def elemByte : wasm_types.ElemType → U8
  | .FuncRef => 0x70#u8 | .ExternRef => 0x6F#u8

/-- A value type as its type byte. -/
def ValueTypeEncoding (ty : wasm_types.ValueType) (bytes : List U8) : Prop :=
  bytes = [valueByte ty]

/-- An element type as its type byte. -/
def ElemTypeEncoding (ty : wasm_types.ElemType) (bytes : List U8) : Prop := bytes = [elemByte ty]

/-- A function type: `0x60`, then the parameter vector and the result vector. -/
def FuncTypeEncoding (ty : wasm_types.FuncType) (bytes : List U8) : Prop :=
  ∃ params results, VecEncoding ValueTypeEncoding ty.params.val params ∧
    VecEncoding ValueTypeEncoding ty.results.val results ∧
    bytes = 0x60#u8 :: (params ++ results)

/-- Limits: flag `0` with a minimum, or flag `1` with a minimum and a maximum. -/
inductive LimitsEncoding : wasm_types.Limits → List U8 → Prop where
  | noMax (min : U32) {bytes} : IndexEncoding min bytes →
      LimitsEncoding ⟨min, none⟩ (0#u8 :: bytes)
  | max (min max : U32) {first rest} : IndexEncoding min first → IndexEncoding max rest →
      LimitsEncoding ⟨min, some max⟩ (1#u8 :: (first ++ rest))

/-- A table type: the element type byte followed by limits. -/
def TableTypeEncoding (ty : wasm_types.TableType) (bytes : List U8) : Prop :=
  ∃ limits, LimitsEncoding ty.limits limits ∧ bytes = elemByte ty.elem :: limits

/-- A memory type is its limits. -/
def MemTypeEncoding (ty : wasm_types.MemType) (bytes : List U8) : Prop :=
  LimitsEncoding ty.limits bytes

/-- The binary mutability byte. -/
def mutByte : wasm_types.Mut → U8 | .Const => 0#u8 | .Var => 1#u8

/-- A global type: the value type byte followed by the mutability byte. -/
def GlobalTypeEncoding (ty : wasm_types.GlobalType) (bytes : List U8) : Prop :=
  bytes = [valueByte ty.valtype, mutByte ty.mutability]

/-- A constant expression: one constant instruction followed by `end` (`0x0b`). -/
inductive ConstEncoding : wasm_types.ConstExpr → List U8 → Prop where
  | i32 (value : I32) {bytes} : SignedLeb32.Encoding bytes value.val →
      ConstEncoding (.I32 value) (0x41#u8 :: (bytes ++ [0x0B#u8]))
  | i64 (value : I64) {bytes} : SignedLeb64.Encoding bytes value.val →
      ConstEncoding (.I64 value) (0x42#u8 :: (bytes ++ [0x0B#u8]))
  | f32 (value : U32) {bytes} : FloatBits.Encoding 4 bytes value.val →
      ConstEncoding (.F32 value) (0x43#u8 :: (bytes ++ [0x0B#u8]))
  | f64 (value : U64) {bytes} : FloatBits.Encoding 8 bytes value.val →
      ConstEncoding (.F64 value) (0x44#u8 :: (bytes ++ [0x0B#u8]))
  | globalGet (index : U32) {bytes} : IndexEncoding index bytes →
      ConstEncoding (.GlobalGet index) (0x23#u8 :: (bytes ++ [0x0B#u8]))
  | refNull (ty : wasm_types.ElemType) :
      ConstEncoding (.RefNull ty) [0xD0#u8, elemByte ty, 0x0B#u8]
  | refFunc (index : U32) {bytes} : IndexEncoding index bytes →
      ConstEncoding (.RefFunc index) (0xD2#u8 :: (bytes ++ [0x0B#u8]))
  | v128 (low high : U64) {sub first rest} :
      IndexEncoding 12#u32 sub → FloatBits.Encoding 8 first low.val →
      FloatBits.Encoding 8 rest high.val →
      ConstEncoding (.V128 low high) (0xFD#u8 :: (sub ++ first ++ rest ++ [0x0B#u8]))

/-- An import descriptor: a kind byte followed by a type index or a table, memory or global type. -/
inductive ImportDescEncoding : metadata.ImportDesc → List U8 → Prop where
  | func (index : U32) {bytes} : IndexEncoding index bytes →
      ImportDescEncoding (.Func index) (0#u8 :: bytes)
  | table (ty : wasm_types.TableType) {bytes} : TableTypeEncoding ty bytes →
      ImportDescEncoding (.Table ty) (1#u8 :: bytes)
  | memory (ty : wasm_types.MemType) {bytes} : MemTypeEncoding ty bytes →
      ImportDescEncoding (.Memory ty) (2#u8 :: bytes)
  | global (ty : wasm_types.GlobalType) {bytes} : GlobalTypeEncoding ty bytes →
      ImportDescEncoding (.Global ty) (3#u8 :: bytes)

/-- An import: module name, field name and descriptor. -/
def ImportEncoding (entry : Import) (bytes : List U8) : Prop :=
  ∃ modname nm desc, NameEncoding entry.moduleName modname ∧
    NameEncoding entry.name nm ∧ ImportDescEncoding entry.desc desc ∧
    bytes = modname ++ nm ++ desc

/-- An export descriptor: a kind byte followed by an index. -/
inductive ExportDescEncoding : metadata.ExportDesc → List U8 → Prop where
  | func (index : U32) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.Func index) (0#u8 :: bytes)
  | table (index : U32) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.Table index) (1#u8 :: bytes)
  | memory (index : U32) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.Memory index) (2#u8 :: bytes)
  | global (index : U32) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.Global index) (3#u8 :: bytes)

/-- An export: name and descriptor. -/
def ExportEncoding (entry : Export) (bytes : List U8) : Prop :=
  ∃ nm desc, NameEncoding entry.name nm ∧ ExportDescEncoding entry.desc desc ∧
    bytes = nm ++ desc

/-- A global: its type followed by its initializer expression. -/
def GlobalEncoding (entry : metadata.Global) (bytes : List U8) : Prop :=
  ∃ ty expr, GlobalTypeEncoding entry.gtype ty ∧ ConstEncoding entry.init expr ∧
    bytes = ty ++ expr

/-- The eight Wasm 2.0 element segment encodings, selected by a flag. Flag and index LEBs need not
be minimal. Index vectors and expression vectors denote the same element syntax. -/
inductive Wasm2ElementEncoding : Element → List U8 → Prop where
  | activeIndices {offset initializers flags encodedOffset entries} :
      IndexEncoding 0#u32 flags → ConstEncoding offset encodedOffset →
      VecEncoding IndexEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Active 0#u32 offset, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (flags ++ encodedOffset ++ entries)
  | passiveIndices {initializers flags entries} :
      IndexEncoding 1#u32 flags → VecEncoding IndexEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Passive, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (flags ++ [0#u8] ++ entries)
  | explicitIndices {tableIndex offset initializers flags table encodedOffset entries} :
      IndexEncoding 2#u32 flags → IndexEncoding tableIndex table →
      ConstEncoding offset encodedOffset → VecEncoding IndexEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Active tableIndex offset, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (flags ++ table ++ encodedOffset ++ [0#u8] ++ entries)
  | declarativeIndices {initializers flags entries} :
      IndexEncoding 3#u32 flags → VecEncoding IndexEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Declarative, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (flags ++ [0#u8] ++ entries)
  | activeExpressions {offset initializers flags encodedOffset entries} :
      IndexEncoding 4#u32 flags → ConstEncoding offset encodedOffset →
      VecEncoding ConstEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Active 0#u32 offset, initializers⟩
        (flags ++ encodedOffset ++ entries)
  | passiveExpressions {elem initializers flags entries} :
      IndexEncoding 5#u32 flags → VecEncoding ConstEncoding initializers entries →
      Wasm2ElementEncoding ⟨elem, .Passive, initializers⟩
        (flags ++ [elemByte elem] ++ entries)
  | explicitExpressions {elem tableIndex offset initializers flags table encodedOffset entries} :
      IndexEncoding 6#u32 flags → IndexEncoding tableIndex table →
      ConstEncoding offset encodedOffset → VecEncoding ConstEncoding initializers entries →
      Wasm2ElementEncoding ⟨elem, .Active tableIndex offset, initializers⟩
        (flags ++ table ++ encodedOffset ++ [elemByte elem] ++ entries)
  | declarativeExpressions {elem initializers flags entries} :
      IndexEncoding 7#u32 flags → VecEncoding ConstEncoding initializers entries →
      Wasm2ElementEncoding ⟨elem, .Declarative, initializers⟩
        (flags ++ [elemByte elem] ++ entries)

/-- The active segment flag forms of a data segment, including non-minimal unsigned LEBs. -/
inductive ActiveIndexEncoding : U32 → Bool → List U8 → Prop where
  | implicit {flags} : IndexEncoding 0#u32 flags → ActiveIndexEncoding 0#u32 false flags
  | explicit {index flags bytes} : IndexEncoding 2#u32 flags → IndexEncoding index bytes →
      ActiveIndexEncoding index true (flags ++ bytes)

/-- The optional explicit table or memory index of an active segment, as selected by the flag. -/
def SegmentIndexEncoding (flags index : U32)
    (explicit : Bool) (bytes : List U8) : Prop :=
  (flags = 0#u32 ∧ index = 0#u32 ∧ explicit = false ∧ bytes = []) ∨
  (flags = 2#u32 ∧ explicit = true ∧ IndexEncoding index bytes)

/-- The Wasm 2.0 element segment grammar. -/
def ElementEncodingFor (entry : Element)
    (bytes : List U8) : Prop :=
  Wasm2ElementEncoding entry bytes

/-- A Wasm 2.0 segment index with its flag is an `ActiveIndexEncoding`. -/
theorem SegmentIndexEncoding.active {flags index explicit bytes headBytes}
    (h : SegmentIndexEncoding flags index explicit bytes)
    (hf : IndexEncoding flags headBytes) : ActiveIndexEncoding index explicit (headBytes ++ bytes) := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, hi⟩
  · simpa using ActiveIndexEncoding.implicit hf
  · exact .explicit hf hi

/-- An `ActiveIndexEncoding` splits into a flag and a Wasm 2.0 `SegmentIndexEncoding`. -/
theorem ActiveIndexEncoding.parts {index explicit bytes}
    (h : ActiveIndexEncoding index explicit bytes) :
    ∃ flags headBytes suffix, IndexEncoding flags headBytes ∧
      SegmentIndexEncoding flags index explicit suffix ∧ bytes = headBytes ++ suffix := by
  cases h with
  | implicit hf => exact ⟨0#u32, _, [], hf, Or.inl ⟨rfl, rfl, rfl, rfl⟩, by simp⟩
  | explicit hf hi => exact ⟨2#u32, _, _, hf, Or.inr ⟨rfl, rfl, hi⟩, rfl⟩

/-- A local declaration: a count followed by a value type byte. -/
def LocalEncoding (entry : U32 × wasm_types.ValueType) (bytes : List U8) : Prop :=
  ∃ count, IndexEncoding entry.1 count ∧ bytes = count ++ [valueByte entry.2]

/-- The Wasm 2.0 data segment encodings: active (flag `0` or `2`) and passive (flag `1`). -/
inductive Wasm2DataEncoding : Data → List U8 → Prop where
  | active {memoryIndex offset init explicit index encodedOffset entries} :
      ActiveIndexEncoding memoryIndex explicit index → ConstEncoding offset encodedOffset →
      ByteVecEncoding init entries →
      Wasm2DataEncoding ⟨.Active memoryIndex offset, init⟩ (index ++ encodedOffset ++ entries)
  | passive {init flags entries} :
      IndexEncoding 1#u32 flags → ByteVecEncoding init entries →
      Wasm2DataEncoding ⟨.Passive, init⟩ (flags ++ entries)

/-- The Wasm 2.0 data segment grammar. -/
def DataEncodingFor (entry : Data) (bytes : List U8) : Prop :=
  Wasm2DataEncoding entry bytes

/-- A section: its id, a LEB128 size equal to the payload length, and the payload. -/
def SectionEncoding {α : Type} (id : U8) (R : α → List U8 → Prop)
    (value : α) (bytes : List U8) : Prop :=
  ∃ size payload, Leb128.Encoding size payload.length ∧ R value payload ∧
    bytes = id :: (size ++ payload)

/-- A custom section: a name followed by arbitrary payload bytes. -/
def CustomEncoding (bytes : List U8) : Prop :=
  ∃ nm payload encodedName,
    NameEncoding nm encodedName ∧
    SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = encodedName ++ payload) () bytes

/-- A sequence of custom sections. -/
inductive CustomsEncoding : List U8 → Prop where
  | nil : CustomsEncoding []
  | cons {first rest} : CustomEncoding first → CustomsEncoding rest →
      CustomsEncoding (first ++ rest)

/-- A section that is either absent, giving the `absent` value, or present. -/
inductive OptionalSectionEncoding {α : Type} (id : U8) (R : α → List U8 → Prop)
    (absent : α) : α → List U8 → Prop where
  | absent : OptionalSectionEncoding id R absent absent []
  | present {value bytes} : SectionEncoding id R value bytes →
      OptionalSectionEncoding id R absent value bytes

/-- An optional section preceded by any number of custom sections. -/
def PaddedEncoding {α : Type} (id : U8) (R : α → List U8 → Prop)
    (absent value : α) (bytes : List U8) : Prop :=
  ∃ customs sec, CustomsEncoding customs ∧
    OptionalSectionEncoding id R absent value sec ∧ bytes = customs ++ sec

/-- Assembles an active data segment from its flag, memory index, offset and
bytes. -/
theorem DataEncodingFor.of_parts {flags memoryIndex explicit offset init fb mb ob ib}
    (hf : IndexEncoding flags fb)
    (hm : SegmentIndexEncoding flags memoryIndex explicit mb)
    (ho : ConstEncoding offset ob) (hi : ByteVecEncoding init ib) :
    DataEncodingFor ⟨.Active memoryIndex offset, init⟩ (fb ++ mb ++ ob ++ ib) := by
  exact .active (hm.active hf) ho hi

/-- The start section payload: a function index. -/
def StartEncoding (value : Option U32) (bytes : List U8) : Prop :=
  ∃ index, value = some index ∧ IndexEncoding index bytes

/-- The module header: the magic number `\0asm` and version 1. -/
def magicVersion : List U8 := [0#u8, 0x61#u8, 0x73#u8, 0x6D#u8, 1#u8, 0#u8, 0#u8, 0#u8]

mutual
  /-- Data indices in instruction syntax trigger the binary data-count requirement. -/
  def instructionUsesData : instr → Bool
    | .MEMORY_INIT _ | .DATA_DROP _ => true
    | .BLOCK _ body | .LOOP _ body => instructionsUseData body
    | .IFELSE _ yes no => instructionsUseData yes || instructionsUseData no
    | _ => false

  /-- Whether any instruction in the list uses a data index. -/
  def instructionsUseData : List instr → Bool
    | [] => false
    | op :: ops => instructionUsesData op || instructionsUseData ops
end

/-- The optional count must match the data section, and every data-indexed body
requires it even when the relevant instruction is nested or unreachable. -/
def DataCountValid (value : Module) : Prop :=
  match value.dataCount with
  | none => ∀ code ∈ value.codes, instructionsUseData code.body = false
  | some count => count.val = value.data.length

/-- Data-count occurs before code despite its numerically larger section ID. -/
def DataCountSectionEncoding (value : Option U32)
    (bytes : List U8) : Prop :=
  PaddedEncoding 12#u8 StartEncoding none value bytes

/-- The Wasm 2.0 module format, parameterized by the code entry grammar, with custom
sections between the ordered optional sections. Typing checks are separate from this grammar. -/
def ModuleEncodingWith (codeRel : Code → List U8 → Prop) (value : Module) (bytes : List U8) : Prop :=
  ∃ types imports functions tables memories globals exports start elements dataCount codes datas customs,
    PaddedEncoding 1#u8 (VecEncoding FuncTypeEncoding) [] value.types types ∧
    PaddedEncoding 2#u8 (VecEncoding ImportEncoding) [] value.imports imports ∧
    PaddedEncoding 3#u8 (VecEncoding IndexEncoding) [] value.functions functions ∧
    PaddedEncoding 4#u8 (VecEncoding TableTypeEncoding) [] value.tables tables ∧
    PaddedEncoding 5#u8 (VecEncoding MemTypeEncoding) [] value.memories memories ∧
    PaddedEncoding 6#u8 (VecEncoding GlobalEncoding) [] value.globals globals ∧
    PaddedEncoding 7#u8 (VecEncoding ExportEncoding) [] value.exports exports ∧
    PaddedEncoding 8#u8 StartEncoding none value.start start ∧
    PaddedEncoding 9#u8 (VecEncoding ElementEncodingFor) [] value.elements elements ∧
    DataCountSectionEncoding value.dataCount dataCount ∧
    PaddedEncoding 10#u8 (VecEncoding codeRel) [] value.codes codes ∧
    PaddedEncoding 11#u8 (VecEncoding DataEncodingFor) [] value.data datas ∧
    CustomsEncoding customs ∧
    bytes = magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
      globals ++ exports ++ start ++ elements ++ dataCount ++ codes ++ datas ++ customs ∧
    DataCountValid value

/-- An `At` interval lies within the buffer. -/
theorem At.span {α : Type} {R : α → List U8 → Prop} {data start value next}
    (h : At R data start value next) : start.val ≤ next.val ∧ next.val ≤ data.length := by
  obtain ⟨bytes, _, hs⟩ := h
  exact ⟨by have := hs.length; omega, hs.bound⟩

/-- `Rep` is closed under concatenation. -/
theorem Rep.append {α : Type} {R : α → List U8 → Prop} {xs ys bs cs}
    (h : Rep R xs bs) (h' : Rep R ys cs) : Rep R (xs ++ ys) (bs ++ cs) := by
  induction h with
  | nil => simpa using h'
  | cons hx _ ih => simpa [List.append_assoc] using Rep.cons hx ih

/-- `Rep` is closed under appending one entry. -/
theorem Rep.snoc {α : Type} {R : α → List U8 → Prop} {xs x bs last}
    (h : Rep R xs bs) (h' : R x last) : Rep R (xs ++ [x]) (bs ++ last) := by
  simpa using h.append (.cons h' .nil)

/-- A `Rep` of raw bytes encodes to the bytes themselves. -/
theorem Rep.bytes {bytes encoded} (h : Rep ByteEncoding bytes encoded) : encoded = bytes := by
  induction h with
  | nil => rfl
  | cons hb _ ih => simp_all [ByteEncoding]

/-- A byte vector is a LEB128 length followed by the bytes. -/
theorem ByteVecEncoding.iff {bytes encoded} : ByteVecEncoding bytes encoded ↔
    ∃ count, Leb128.Encoding count bytes.length ∧ encoded = count ++ bytes := by
  constructor
  · rintro ⟨count, entries, hc, hr, rfl⟩
    exact ⟨count, hc, by rw [hr.bytes]⟩
  · rintro ⟨count, hc, rfl⟩
    refine ⟨count, bytes, hc, ?_, rfl⟩
    clear hc
    induction bytes with
    | nil => exact .nil
    | cons b bs ih => exact .cons (show ByteEncoding b [b] from rfl) ih

end Itasca.ModuleBinary

end

/-! ## PrefixUnique -/

section

/-!
# Prefix uniqueness of the binary grammar

Defines `PrefixUnique` and `Unique` for byte-level relations and shows that they are preserved by
sequences (`PrefixUnique.rep`, `PrefixUnique.rep_unique`) and vectors (`PrefixUnique.vec`). Proves
`PrefixUnique` for the primitive encodings: LEB128 integers, indices, bytes, names and float bits.
Prefix uniqueness is what makes concatenated encodings decode in only one way.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- An encoding relation determines both the value and the consumed prefix of any byte string that
starts with an encoding. Suffixes are arbitrary lists, with no implementation bound. -/
def PrefixUnique {α : Type} (R : α → List U8 → Prop) : Prop :=
  ∀ ⦃x y first second rest tail⦄, R x first → R y second →
    first ++ rest = second ++ tail → x = y ∧ first = second ∧ rest = tail

/-- An encoding relation determines its value from the complete byte string. -/
def Unique {α : Type} (R : α → List U8 → Prop) : Prop :=
  ∀ ⦃x y bytes⦄, R x bytes → R y bytes → x = y

/-- Prefix uniqueness implies uniqueness. -/
theorem PrefixUnique.unique {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) : Unique R := by
  intro x y bytes hx hy
  exact (h hx hy (rest := []) (tail := []) rfl).1

/-- Equal-length prefixes of equal lists are equal, and so are the remainders. -/
theorem split_of_length {α : Type} {xs ys rest tail : List α}
    (he : xs ++ rest = ys ++ tail) (hl : xs.length = ys.length) :
    xs = ys ∧ rest = tail := by
  have h := congrArg (List.take xs.length) he
  have hx : xs = ys := by simpa [List.take_append, hl] using h
  subst ys
  exact ⟨rfl, List.append_cancel_left he⟩

/-- Prefix uniqueness extends to sequences of the same length. -/
theorem PrefixUnique.rep {α : Type} {R : α → List U8 → Prop} (h : PrefixUnique R)
    {xs ys first second rest tail} (hx : Rep R xs first) (hy : Rep R ys second)
    (hl : xs.length = ys.length) (he : first ++ rest = second ++ tail) :
    xs = ys ∧ first = second ∧ rest = tail := by
  induction hx generalizing ys second with
  | nil =>
    cases hy with
    | nil => exact ⟨rfl, rfl, he⟩
    | cons => simp at hl
  | @cons x xs a b ha hb ih =>
    cases hy with
    | nil => simp at hl
    | @cons y ys c d hc hd =>
      obtain ⟨rfl, rfl, ht⟩ := h ha hc (by simpa [List.append_assoc] using he)
      obtain ⟨rfl, rfl, rfl⟩ := ih hd (by simpa using hl) ht
      exact ⟨rfl, rfl, rfl⟩

/-- A prefix-unique relation with nonempty encodings gives unique sequence encodings. -/
theorem PrefixUnique.rep_unique {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) (hn : ∀ x bs, R x bs → bs ≠ []) : Unique (Rep R) := by
  intro xs ys bytes hx hy
  generalize he : bytes = other at hy
  induction hx generalizing ys other with
  | nil =>
    cases hy with
    | nil => rfl
    | @cons y ys a b ha hb =>
      exact False.elim (hn y a ha (List.append_eq_nil_iff.mp he.symm).1)
  | @cons x xs a b ha hb ih =>
    cases hy with
    | nil =>
      exact False.elim (hn x a ha (List.append_eq_nil_iff.mp he).1)
    | @cons y ys c d hc hd =>
      obtain ⟨rfl, rfl, rfl⟩ := h ha hc he
      exact congrArg (List.cons x) (ih b rfl hd)

/-- Unsigned LEB128 encodings are prefix-unique. -/
theorem leb_prefix_unique : PrefixUnique (fun n bs => Leb128.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Leb128.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

/-- Index encodings are prefix-unique. -/
theorem index_prefix_unique : PrefixUnique IndexEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨hv, rfl, ht⟩ := leb_prefix_unique hx hy he
  exact ⟨UScalar.eq_of_val_eq hv, rfl, ht⟩

/-- Vector encodings of a prefix-unique relation are prefix-unique. -/
theorem PrefixUnique.vec {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) : PrefixUnique (VecEncoding R) := by
  intro xs ys a b rest tail hx hy he
  obtain ⟨n, entries, hn, hx, rfl⟩ := hx
  obtain ⟨m, entries', hm, hy, rfl⟩ := hy
  obtain ⟨hl, rfl, ht⟩ := leb_prefix_unique hn hm (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := h.rep hx hy hl ht
  exact ⟨rfl, rfl, rfl⟩

/-- Raw byte encodings are prefix-unique. -/
theorem byte_prefix_unique : PrefixUnique ByteEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  exact ⟨rfl, rfl, rfl⟩

/-- Name encodings are prefix-unique. -/
theorem name_prefix_unique : PrefixUnique NameEncoding := by
  intro x y a b rest tail hx hy he
  exact byte_prefix_unique.vec hx.1 hy.1 he

/-- Fixed-width float bit pattern encodings are prefix-unique. -/
theorem float_prefix_unique (n : Nat) :
    PrefixUnique (fun bits bs => FloatBits.Encoding n bs bits) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := split_of_length he (hx.1.trans hy.1.symm)
  exact ⟨hx.2.trans hy.2.symm, rfl, rfl⟩

/-- Signed 32-bit LEB128 encodings are prefix-unique. -/
theorem signed32_prefix_unique : PrefixUnique (fun n bs => SignedLeb32.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := SignedLeb32.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

/-- Signed 64-bit LEB128 encodings are prefix-unique. -/
theorem signed64_prefix_unique : PrefixUnique (fun n bs => SignedLeb64.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := SignedLeb64.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

end Itasca.ModuleBinary

end

/-! ## Unicode -/

section

/-!
# Unicode semantics of names

Connects the byte-level `Utf8` grammar to the generated specification's `fun_utf8` relation.
`decodeChars` decodes strict UTF-8, `Utf8.semantic` shows that accepted bytes denote the decoded
string and `NameEncoding.wellFormed` shows that a binary name satisfies `wf_name`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A byte as a generated-specification `byte`. -/
def specByte (b : U8) : byte := .mk_byte b.val

/-- Every byte is well formed. -/
theorem specByte_wf (b : U8) : wf_byte (specByte b) := by
  apply wf_byte.byte_case_0
  scalar_tac

/-- Decodes UTF-8 bytes to Unicode scalars. It is only meaningful on bytes accepted by `Utf8`,
whose grammar excludes malformed sequences. -/
def decodeChars : List U8 → List char
  | [] => []
  | a :: rest =>
      if a.val < 128 then .mk_char a.val :: decodeChars rest
      else match rest with
        | [] => []
        | b :: rest =>
            if a.val < 224 then .mk_char (64 * (a.val - 192) + (b.val - 128)) :: decodeChars rest
            else match rest with
              | [] => []
              | c :: rest =>
                  if a.val < 240 then
                    .mk_char (4096 * (a.val - 224) + 64 * (b.val - 128) + (c.val - 128)) :: decodeChars rest
                  else match rest with
                    | [] => []
                    | d :: rest =>
                        .mk_char (262144 * (a.val - 240) + 4096 * (b.val - 128) +
                          64 * (c.val - 128) + (d.val - 128)) :: decodeChars rest

/-- The generated-specification name denoted by UTF-8 name bytes. -/
def nameOfBytes (bytes : List U8) : «name» := .mk_name (decodeChars bytes)

/-- Each `Utf8Char` sequence decodes to one well-formed Unicode scalar related to its bytes by
`fun_utf8`. -/
theorem Utf8Char.semantic {bytes : List U8} (h : Utf8Char bytes) (rest : List U8) :
    ∃ ch, decodeChars (bytes ++ rest) = ch :: decodeChars rest ∧
      fun_utf8 [ch] (bytes.map specByte) ∧ wf_char ch := by
  cases h with
  | one a ha =>
      refine ⟨.mk_char a.val, ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, (_ | ⟨y, (_ | ⟨z, tail⟩)⟩)⟩ <;>
          simp [decodeChars, show a.val < 128 by omega]
      · exact .fun_utf8_case_0 _ _ ⟨ha.trans_lt (by decide), rfl⟩ (specByte_wf a) (specByte_wf a)
      · apply wf_char.char_case_0; omega
  | two a b ha ha' hb hb' =>
      refine ⟨.mk_char (64 * (a.val - 192) + (b.val - 128)), ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, (_ | ⟨y, tail⟩)⟩ <;>
          simp [decodeChars, show ¬a.val < 128 by omega, show a.val < 224 by omega]
      · apply fun_utf8.fun_utf8_case_1 _ _ _ ?_ (specByte_wf a) (specByte_wf b)
        simp only [proj_char_0, specByte, proj_byte_0]
        omega
      · apply wf_char.char_case_0; omega
  | three a b c ha hc hc' =>
      refine ⟨.mk_char (4096 * (a.val - 224) + 64 * (b.val - 128) + (c.val - 128)), ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, tail⟩ <;>
          simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
            show a.val < 240 by omega]
      · apply fun_utf8.fun_utf8_case_2 _ _ _ _ ?_ (specByte_wf a) (specByte_wf b) (specByte_wf c)
        simp only [proj_char_0, specByte, proj_byte_0]
        omega
      · apply wf_char.char_case_0; omega
  | four a b c d ha hc hc' hd hd' =>
      refine ⟨.mk_char (262144 * (a.val - 240) + 4096 * (b.val - 128) +
        64 * (c.val - 128) + (d.val - 128)), ?_, ?_, ?_⟩
      · simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
          show ¬a.val < 240 by omega]
      · apply fun_utf8.fun_utf8_case_3 _ _ _ _ _ ?_ (specByte_wf a) (specByte_wf b)
          (specByte_wf c) (specByte_wf d)
        simp only [proj_char_0, specByte, proj_byte_0]
        omega
      · apply wf_char.char_case_0; omega

private theorem Utf8.chunks {bytes : List U8} (h : Utf8 bytes) :
    ∃ chunks, chunks.length = (decodeChars bytes).length ∧
      Forall₂ (fun bs ch => fun_utf8 [ch] bs) chunks (decodeChars bytes) ∧
      concat_ byte chunks = bytes.map specByte ∧ Forall wf_char (decodeChars bytes) := by
  induction h with
  | nil => exact ⟨[], rfl, by simp [Forall₂, decodeChars], rfl, by simp [Forall, decodeChars]⟩
  | @cons first rest hc hr ih =>
      obtain ⟨ch, hd, he, hw⟩ := hc.semantic rest
      obtain ⟨chunks, hl, hh, hb, hw'⟩ := ih
      refine ⟨first.map specByte :: chunks, ?_, ?_, ?_, ?_⟩
      · simp [hd, hl]
      · simp only [hd, Forall₂, List.zip_cons_cons, List.mem_cons]
        intro pair hm
        rcases hm with rfl | hm
        · exact he
        · exact hh pair hm
      · simp [concat_, hb, List.map_append]
      · simp only [hd, Forall, List.mem_cons]
        intro c hm
        rcases hm with rfl | hm
        · exact hw
        · exact hw' c hm

private theorem concat_flatten (chunks : List (List byte)) : concat_ byte chunks = chunks.flatten := by
  induction chunks with
  | nil => rfl
  | cons head tail ih => simp [concat_, ih]

/-- Accepted UTF-8 bytes are related by `fun_utf8` to the string `decodeChars` computes, and each
scalar is well formed. -/
theorem Utf8.semantic {bytes : List U8} (h : Utf8 bytes) :
    fun_utf8 (decodeChars bytes) (bytes.map specByte) ∧ Forall wf_char (decodeChars bytes) := by
  obtain ⟨chunks, hl, hh, hb, hw⟩ := h.chunks
  have hbytes : Forall wf_byte (concat_ byte chunks) := by
    rw [hb]
    intro b hm
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hm
    exact specByte_wf source
  have hnested : Forall (fun bs => Forall wf_byte bs) chunks := by
    intro bs hbs b hmem
    apply hbytes b
    rw [concat_flatten]
    exact List.mem_flatten.mpr ⟨bs, hbs, hmem⟩
  refine ⟨?_, hw⟩
  rw [← hb]
  exact fun_utf8.fun_utf8_case_4 _ chunks chunks chunks hl hh hl hh hl hh hbytes hnested

/-- A binary name denotes a well-formed generated-specification name, including its UTF-8 byte
size bound. -/
theorem NameEncoding.wellFormed {nm bytes} (h : NameEncoding nm bytes) :
    wf_name (nameOfBytes nm) := by
  obtain ⟨count, hcount, _⟩ := ByteVecEncoding.iff.mp h.1
  obtain ⟨hutf, hw⟩ := h.2.semantic
  apply wf_name.name_case_0 _ (nm.map specByte) hutf hw
  simpa using Leb128.Encoding.value_lt hcount

end Itasca.ModuleBinary

end

/-! ## UnicodeUnique -/

section

/-!
# Uniqueness of decoded names

Shows that `decodeChars` is injective on bytes accepted by `Utf8`, by re-encoding scalars
canonically (`Utf8.roundtrip`). `Utf8.nameOfBytes_injective` transports the validator's
duplicate-name check on raw bytes to equality of Unicode names.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The shortest UTF-8 encoding of a scalar, as natural numbers. -/
def encodeChar : char → List Nat
  | .mk_char n =>
      if n < 128 then [n]
      else if n < 2048 then [192 + n / 64, 128 + n % 64]
      else if n < 65536 then [224 + n / 4096, 128 + n / 64 % 64, 128 + n % 64]
      else [240 + n / 262144, 128 + n / 4096 % 64, 128 + n / 64 % 64, 128 + n % 64]

private theorem encode_two (a b : Nat) (ha : 194 ≤ a) (ha' : a ≤ 223)
    (hb : 128 ≤ b) (hb' : b ≤ 191) :
    encodeChar (.mk_char (64 * (a - 192) + (b - 128))) = [a, b] := by
  have hlo : ¬64 * (a - 192) + (b - 128) < 128 := by omega
  have hhi : 64 * (a - 192) + (b - 128) < 2048 := by omega
  simp [encodeChar, hlo, hhi]
  omega

private theorem encode_three (a b c : Nat)
    (ha : (a = 224 ∧ 160 ≤ b ∧ b ≤ 191) ∨
      (225 ≤ a ∧ a ≤ 236 ∧ 128 ≤ b ∧ b ≤ 191) ∨
      (a = 237 ∧ 128 ≤ b ∧ b ≤ 159) ∨
      (238 ≤ a ∧ a ≤ 239 ∧ 128 ≤ b ∧ b ≤ 191))
    (hc : 128 ≤ c) (hc' : c ≤ 191) :
    encodeChar (.mk_char (4096 * (a - 224) + 64 * (b - 128) + (c - 128))) = [a, b, c] := by
  have hlo : ¬4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 128 := by omega
  have hlo' : ¬4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 2048 := by omega
  have hhi : 4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 65536 := by omega
  simp [encodeChar, hlo, hlo', hhi]
  omega

private theorem encode_four (a b c d : Nat)
    (ha : (a = 240 ∧ 144 ≤ b ∧ b ≤ 191) ∨
      (241 ≤ a ∧ a ≤ 243 ∧ 128 ≤ b ∧ b ≤ 191) ∨
      (a = 244 ∧ 128 ≤ b ∧ b ≤ 143))
    (hc : 128 ≤ c) (hc' : c ≤ 191) (hd : 128 ≤ d) (hd' : d ≤ 191) :
    encodeChar (.mk_char (262144 * (a - 240) + 4096 * (b - 128) +
      64 * (c - 128) + (d - 128))) = [a, b, c, d] := by
  have hlo : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 128 := by omega
  have hlo' : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 2048 := by omega
  have hlo'' : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 65536 := by omega
  simp [encodeChar, hlo, hlo', hlo'']
  omega

/-- Decoding a `Utf8Char` sequence and re-encoding the scalar recovers its bytes. -/
theorem Utf8Char.roundtrip {bytes} (h : Utf8Char bytes) (rest : List U8) :
    (decodeChars (bytes ++ rest)).flatMap encodeChar =
      bytes.map UScalar.val ++ (decodeChars rest).flatMap encodeChar := by
  cases h with
  | one a ha =>
      rcases rest with _ | ⟨x, (_ | ⟨y, (_ | ⟨z, tail⟩)⟩)⟩ <;>
        simp [decodeChars, show a.val < 128 by omega, encodeChar]
  | two a b ha ha' hb hb' =>
      have he := encode_two a.val b.val ha ha' hb hb'
      rcases rest with _ | ⟨x, (_ | ⟨y, tail⟩)⟩ <;>
        simp [decodeChars, show ¬a.val < 128 by omega, show a.val < 224 by omega, he]
  | three a b c ha hc hc' =>
      have he := encode_three a.val b.val c.val ha hc hc'
      rcases rest with _ | ⟨x, tail⟩ <;>
        simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
          show a.val < 240 by omega, he]
  | four a b c d ha hc hc' hd hd' =>
      have he := encode_four a.val b.val c.val d.val ha hc hc' hd hd'
      simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
        show ¬a.val < 240 by omega, he]

/-- Decoding accepted UTF-8 and re-encoding each scalar recovers the original bytes. -/
theorem Utf8.roundtrip {bytes} (h : Utf8 bytes) :
    (decodeChars bytes).flatMap encodeChar = bytes.map UScalar.val := by
  induction h with
  | nil => rfl
  | cons hc _ ih => rw [hc.roundtrip, ih, List.map_append]

/-- `decodeChars` is injective on accepted UTF-8. -/
theorem Utf8.decodeChars_injective {first rest} (h : Utf8 first) (h' : Utf8 rest)
    (heq : decodeChars first = decodeChars rest) : first = rest := by
  have hbytes : first.map UScalar.val = rest.map UScalar.val := by
    rw [← h.roundtrip, heq, h'.roundtrip]
  clear h h' heq
  induction first generalizing rest with
  | nil => cases rest <;> simp_all
  | cons a first ih =>
      cases rest with
      | nil => simp at hbytes
      | cons b rest =>
          obtain ⟨ha, ht⟩ := List.cons.inj hbytes
          rw [UScalar.eq_of_val_eq ha, ih ht]

/-- For names the binary grammar accepts, equal Unicode names have equal bytes. -/
theorem Utf8.nameOfBytes_injective {first rest} (h : Utf8 first) (h' : Utf8 rest)
    (heq : nameOfBytes first = nameOfBytes rest) : first = rest := by
  exact h.decodeChars_injective h' («name».mk_name.inj heq)

end Itasca.ModuleBinary

end
