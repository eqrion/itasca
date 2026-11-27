import WebAssembly.Binary.Instructions
import WebAssembly.Binary.DataCount

namespace WebAssembly.Binary

/-- Names in import and export entries retain their UTF-8 bytes. Function import
descriptors retain the type index until module elaboration. -/
inductive ImportDesc where
  | Func (index : Nat)
  | Table (ty : tabletype)
  | Memory (ty : memtype)
  | Global (ty : globaltype)

/-- The raw form preserves scalar literal bits and the two halves of a vector literal. -/
inductive ConstExpr where
  | I32 (value : Int)
  | I64 (value : Int)
  | F32 (bits : Nat)
  | F64 (bits : Nat)
  | V128 (low high : Nat)
  | GlobalGet (index : Nat)
  | RefNull (ty : reftype)
  | RefFunc (index : Nat)

structure Global where
  gtype : globaltype
  init : ConstExpr

inductive ElementMode where
  | Active (index : Nat) (offset : ConstExpr)
  | Passive | Declarative

inductive DataMode where
  | Active (index : Nat) (offset : ConstExpr)
  | Passive

/-- Raw module syntax keeps indices as written and locals in their binary groups. Names are bytes;
their Unicode validity is a separate judgment (`NameEncoding`). -/
structure Import where
  moduleName : List UInt8
  «name» : List UInt8
  desc : ImportDesc

/-- A raw export: a byte-string name and its descriptor. -/
structure Export where
  «name» : List UInt8
  desc : externidx

/-- A raw element segment: element type, mode and initializer expressions. -/
structure Element where
  elem : reftype
  mode : ElementMode
  init : List ConstExpr

/-- A raw code entry: grouped local declarations and the structured body. -/
structure Code where
  locals : List (Nat × ValueType)
  body : List instr

/-- The flattened local types declared by a code entry. -/
def Code.declared (entry : Code) : List ValueType :=
  entry.locals.flatMap (fun (count, ty) => List.replicate count ty)

/-- A raw data segment: its mode and the initializer bytes. -/
structure Data where
  mode : DataMode
  init : List UInt8

/-- A raw module: the decoded contents of every section, before any typing check. -/
structure Module where
  types : List functype
  imports : List Import
  functions : List Nat
  tables : List tabletype
  memories : List memtype
  globals : List Global
  exports : List Export
  start : Option Nat
  elements : List Element
  dataCount : Option Nat
  codes : List Code
  data : List Data

/-- Concatenate one byte span per value, preserving order. -/
inductive Rep {α β : Type} (R : α → List β → Prop) : List α → List β → Prop where
  | nil : Rep R [] []
  | cons {value values first rest} : R value first → Rep R values rest →
      Rep R (value :: values) (first ++ rest)

/-- A vector: a `u32` LEB128 count equal to the length, followed by the entries' encodings. -/
def VecEncodingWith {α β : Type} (countEncoding : List β → Nat → Prop)
    (R : α → List β → Prop) (values : List α) (bytes : List β) : Prop :=
  ∃ count entries, countEncoding count values.length ∧ Rep R values entries ∧
    bytes = count ++ entries

abbrev VecEncoding {α : Type} := @VecEncodingWith α UInt8 Leb128.U32Encoding

/-- An index as an unsigned LEB128 `u32`. -/
def IndexEncoding (index : Nat) (bytes : List UInt8) : Prop :=
  Leb128.U32Encoding bytes index

/-- A single raw byte. -/
def ByteEncoding {β : Type} (byte : β) (bytes : List β) : Prop := bytes = [byte]

/-- A vector of raw bytes. -/
abbrev ByteVecEncodingWith {β : Type} (countEncoding : List β → Nat → Prop) :=
  VecEncodingWith countEncoding ByteEncoding

abbrev ByteVecEncoding := ByteVecEncodingWith Leb128.U32Encoding

/-- A Unicode scalar's shortest UTF-8 byte sequence. The bounds exclude
surrogates, overlong sequences, and scalar values above U+10FFFF. -/
inductive Utf8CharWith {β : Type} (byte : β → Nat) : List β → Prop where
  | one (a : β) : byte a ≤ 0x7F → Utf8CharWith byte [a]
  | two (a b : β) : 0xC2 ≤ byte a → byte a ≤ 0xDF →
      0x80 ≤ byte b → byte b ≤ 0xBF → Utf8CharWith byte [a, b]
  | three (a b c : β) :
      ((byte a = 0xE0 ∧ 0xA0 ≤ byte b ∧ byte b ≤ 0xBF) ∨
       (0xE1 ≤ byte a ∧ byte a ≤ 0xEC ∧ 0x80 ≤ byte b ∧ byte b ≤ 0xBF) ∨
       (byte a = 0xED ∧ 0x80 ≤ byte b ∧ byte b ≤ 0x9F) ∨
       (0xEE ≤ byte a ∧ byte a ≤ 0xEF ∧ 0x80 ≤ byte b ∧ byte b ≤ 0xBF)) →
      0x80 ≤ byte c → byte c ≤ 0xBF → Utf8CharWith byte [a, b, c]
  | four (a b c d : β) :
      ((byte a = 0xF0 ∧ 0x90 ≤ byte b ∧ byte b ≤ 0xBF) ∨
       (0xF1 ≤ byte a ∧ byte a ≤ 0xF3 ∧ 0x80 ≤ byte b ∧ byte b ≤ 0xBF) ∨
       (byte a = 0xF4 ∧ 0x80 ≤ byte b ∧ byte b ≤ 0x8F)) →
      0x80 ≤ byte c → byte c ≤ 0xBF → 0x80 ≤ byte d → byte d ≤ 0xBF →
      Utf8CharWith byte [a, b, c, d]

/-- A concatenation of `Utf8Char` sequences. -/
inductive Utf8With {β : Type} (byte : β → Nat) : List β → Prop where
  | nil : Utf8With byte []
  | cons {first rest} : Utf8CharWith byte first → Utf8With byte rest → Utf8With byte (first ++ rest)

abbrev Utf8Char := Utf8CharWith UInt8.toNat
abbrev Utf8 := Utf8With UInt8.toNat

/-- A name: a byte vector whose contents are valid UTF-8. -/
def NameEncodingWith {β : Type} (byte : β → Nat) (countEncoding : List β → Nat → Prop)
    (nm bytes : List β) : Prop := ByteVecEncodingWith countEncoding nm bytes ∧ Utf8With byte nm

abbrev NameEncoding := NameEncodingWith UInt8.toNat Leb128.U32Encoding

/-- The binary type byte of a reference element type. -/

def ValueTypeEncoding (ty : valtype) (bytes : List UInt8) : Prop :=
  ∃ t : ValueType, ty = t.toSpec ∧ bytes = [valueByte t]

def FuncTypeEncoding : functype → List UInt8 → Prop
  | .mk_functype (.mk_list params) (.mk_list results), bytes =>
    ∃ ps rs, VecEncoding ValueTypeEncoding params ps ∧ VecEncoding ValueTypeEncoding results rs ∧
      bytes = 0x60 :: (ps ++ rs)

inductive LimitsEncoding : limits → List UInt8 → Prop where
  | noMax (min : Nat) {bytes} : IndexEncoding min bytes →
      LimitsEncoding (.mk_limits (.mk_uN min) none) (0 :: bytes)
  | max (min max : Nat) {first rest} : IndexEncoding min first → IndexEncoding max rest →
      LimitsEncoding (.mk_limits (.mk_uN min) (some (.mk_uN max))) (1 :: (first ++ rest))

def TableTypeEncoding : tabletype → List UInt8 → Prop
  | .mk_tabletype lim rt, bytes =>
    ∃ encoded, LimitsEncoding lim encoded ∧ bytes = ReferencesBinary.referenceByte rt :: encoded

def MemTypeEncoding : memtype → List UInt8 → Prop
  | .PAGE lim, bytes => LimitsEncoding lim bytes

def mutabilityByte (m : «mut») : UInt8 := if m.isSome then 1 else 0

def GlobalTypeEncoding : globaltype → List UInt8 → Prop
  | .mk_globaltype mutability ty, bytes =>
    ∃ t : ValueType, ty = t.toSpec ∧
      bytes = [valueByte t, mutabilityByte mutability]

/-- A constant expression: one constant instruction followed by `end` (`0x0b`). -/
inductive ConstEncoding : ConstExpr → List UInt8 → Prop where
  | i32 (value : Int) {bytes} : Leb128.S32Encoding bytes value →
      ConstEncoding (.I32 value) (0x41 :: (bytes ++ [0x0B]))
  | i64 (value : Int) {bytes} : Leb128.S64Encoding bytes value →
      ConstEncoding (.I64 value) (0x42 :: (bytes ++ [0x0B]))
  | f32 (value : Nat) {bytes} : FloatBits.Encoding 4 bytes value →
      ConstEncoding (.F32 value) (0x43 :: (bytes ++ [0x0B]))
  | f64 (value : Nat) {bytes} : FloatBits.Encoding 8 bytes value →
      ConstEncoding (.F64 value) (0x44 :: (bytes ++ [0x0B]))
  | globalGet (index : Nat) {bytes} : IndexEncoding index bytes →
      ConstEncoding (.GlobalGet index) (0x23 :: (bytes ++ [0x0B]))
  | refNull (ty : reftype) :
      ConstEncoding (.RefNull ty) [0xD0, ReferencesBinary.referenceByte ty, 0x0B]
  | refFunc (index : Nat) {bytes} : IndexEncoding index bytes →
      ConstEncoding (.RefFunc index) (0xD2 :: (bytes ++ [0x0B]))
  | v128 (low high : Nat) {sub first rest} :
      IndexEncoding 12 sub → FloatBits.Encoding 8 first low →
      FloatBits.Encoding 8 rest high →
      ConstEncoding (.V128 low high) (0xFD :: (sub ++ first ++ rest ++ [0x0B]))

/-- An import descriptor: a kind byte followed by a type index or a table, memory or global type. -/
inductive ImportDescEncoding : ImportDesc → List UInt8 → Prop where
  | func (index : Nat) {bytes} : IndexEncoding index bytes →
      ImportDescEncoding (.Func index) (0 :: bytes)
  | table (ty : tabletype) {bytes} : TableTypeEncoding ty bytes →
      ImportDescEncoding (.Table ty) (1 :: bytes)
  | memory (ty : memtype) {bytes} : MemTypeEncoding ty bytes →
      ImportDescEncoding (.Memory ty) (2 :: bytes)
  | global (ty : globaltype) {bytes} : GlobalTypeEncoding ty bytes →
      ImportDescEncoding (.Global ty) (3 :: bytes)

/-- An import: module name, field name and descriptor. -/
def ImportEncoding (entry : Import) (bytes : List UInt8) : Prop :=
  ∃ modname nm desc, NameEncoding entry.moduleName modname ∧
    NameEncoding entry.name nm ∧ ImportDescEncoding entry.desc desc ∧
    bytes = modname ++ nm ++ desc

/-- An export descriptor: a kind byte followed by an index. -/
inductive ExportDescEncoding : externidx → List UInt8 → Prop where
  | func (index : Nat) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.FUNC (.mk_uN index)) (0 :: bytes)
  | table (index : Nat) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.TABLE (.mk_uN index)) (1 :: bytes)
  | memory (index : Nat) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.MEM (.mk_uN index)) (2 :: bytes)
  | global (index : Nat) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.GLOBAL (.mk_uN index)) (3 :: bytes)

/-- An export: name and descriptor. -/
def ExportEncoding (entry : Export) (bytes : List UInt8) : Prop :=
  ∃ nm desc, NameEncoding entry.name nm ∧ ExportDescEncoding entry.desc desc ∧
    bytes = nm ++ desc

/-- A global: its type followed by its initializer expression. -/
def GlobalEncoding (entry : Global) (bytes : List UInt8) : Prop :=
  ∃ ty expr, GlobalTypeEncoding entry.gtype ty ∧ ConstEncoding entry.init expr ∧
    bytes = ty ++ expr

/-- The eight element segment flags and their header immediates. -/
inductive ElementHeaderEncoding : ElementMode → reftype → Bool → List UInt8 → Prop where
  | activeIndices {offset fb ob} : IndexEncoding 0 fb → ConstEncoding offset ob →
      ElementHeaderEncoding (.Active 0 offset) .FUNCREF false (fb ++ ob)
  | passiveIndices {fb} : IndexEncoding 1 fb →
      ElementHeaderEncoding .Passive .FUNCREF false (fb ++ [0])
  | explicitIndices {index offset fb ib ob} : IndexEncoding 2 fb →
      IndexEncoding index ib → ConstEncoding offset ob →
      ElementHeaderEncoding (.Active index offset) .FUNCREF false (fb ++ ib ++ ob ++ [0])
  | declarativeIndices {fb} : IndexEncoding 3 fb →
      ElementHeaderEncoding .Declarative .FUNCREF false (fb ++ [0])
  | activeExpressions {offset fb ob} : IndexEncoding 4 fb → ConstEncoding offset ob →
      ElementHeaderEncoding (.Active 0 offset) .FUNCREF true (fb ++ ob)
  | passiveExpressions {elem fb} : IndexEncoding 5 fb →
      ElementHeaderEncoding .Passive elem true (fb ++ [ReferencesBinary.referenceByte elem])
  | explicitExpressions {elem index offset fb ib ob} : IndexEncoding 6 fb →
      IndexEncoding index ib → ConstEncoding offset ob →
      ElementHeaderEncoding (.Active index offset) elem true (fb ++ ib ++ ob ++ [ReferencesBinary.referenceByte elem])
  | declarativeExpressions {elem fb} : IndexEncoding 7 fb →
      ElementHeaderEncoding .Declarative elem true (fb ++ [ReferencesBinary.referenceByte elem])

def InitializerEncoding (expressions : Bool) (value : ConstExpr) (bytes : List UInt8) : Prop :=
  if expressions then ConstEncoding value bytes
  else ∃ index, value = .RefFunc index ∧ IndexEncoding index bytes

def ElementEncoding (entry : Element) (bs : List UInt8) : Prop :=
  ∃ expressions header init, ElementHeaderEncoding entry.mode entry.elem expressions header ∧
    VecEncoding (InitializerEncoding expressions) entry.init init ∧ bs = header ++ init

/-- The active segment flag forms of a data segment, including non-minimal unsigned LEBs. -/
inductive ActiveIndexEncoding : Nat → Bool → List UInt8 → Prop where
  | implicit {flags} : IndexEncoding 0 flags → ActiveIndexEncoding 0 false flags
  | explicit {index flags bytes} : IndexEncoding 2 flags → IndexEncoding index bytes →
      ActiveIndexEncoding index true (flags ++ bytes)

/-- A local declaration: a count followed by a value type byte. -/
def LocalEncoding (entry : Nat × ValueType) (bytes : List UInt8) : Prop :=
  ∃ count, IndexEncoding entry.1 count ∧ bytes = count ++ [valueByte entry.2]

/-- The Wasm 2.0 data segment encodings: active (flag `0` or `2`) and passive (flag `1`). -/
inductive DataEncoding : Data → List UInt8 → Prop where
  | active {memoryIndex offset init explicit index encodedOffset entries} :
      ActiveIndexEncoding memoryIndex explicit index → ConstEncoding offset encodedOffset →
      ByteVecEncoding init entries →
      DataEncoding ⟨.Active memoryIndex offset, init⟩ (index ++ encodedOffset ++ entries)
  | passive {init flags entries} :
      IndexEncoding 1 flags → ByteVecEncoding init entries →
      DataEncoding ⟨.Passive, init⟩ (flags ++ entries)

/-- A section carries its ID, the encoded payload size, and that many payload bytes. -/
def SectionEncodingWith {α β : Type} (sizeEncoding : List β → Nat → Prop)
    (id : β) (R : α → List β → Prop) (value : α) (bytes : List β) : Prop :=
  ∃ size payload, sizeEncoding size payload.length ∧ R value payload ∧ bytes = id :: (size ++ payload)

/-- A custom section contains a name followed by uninterpreted bytes. -/
def CustomEncodingWith {β : Type} (byte : β → Nat) (ofByte : UInt8 → β)
    (size : List β → Nat → Prop) (bytes : List β) : Prop :=
  ∃ nm payload encodedName, NameEncodingWith byte size nm encodedName ∧
    SectionEncodingWith size (ofByte 0) (fun (_ : Unit) bs => bs = encodedName ++ payload) () bytes

inductive CustomsEncodingWith {β : Type} (custom : List β → Prop) : List β → Prop where
  | nil : CustomsEncodingWith custom []
  | cons {first rest} : custom first → CustomsEncodingWith custom rest → CustomsEncodingWith custom (first ++ rest)

inductive OptionalSectionEncodingWith {α β : Type} (size : List β → Nat → Prop)
    (id : β) (R : α → List β → Prop) (absent : α) : α → List β → Prop where
  | absent : OptionalSectionEncodingWith size id R absent absent []
  | present {value bytes} : SectionEncodingWith size id R value bytes →
      OptionalSectionEncodingWith size id R absent value bytes

def PaddedEncodingWith {α β : Type} (custom : List β → Prop) (size : List β → Nat → Prop)
    (id : β) (R : α → List β → Prop) (absent value : α) (bytes : List β) : Prop :=
  ∃ customs sec, CustomsEncodingWith custom customs ∧
    OptionalSectionEncodingWith size id R absent value sec ∧ bytes = customs ++ sec

def StartEncodingWith {α β : Type} (indexEncoding : α → List β → Prop)
    (value : Option α) (bytes : List β) : Prop :=
  ∃ index, value = some index ∧ indexEncoding index bytes

abbrev SectionEncoding {α : Type} := @SectionEncodingWith α UInt8 Leb128.U32Encoding
abbrev CustomEncoding := CustomEncodingWith UInt8.toNat id Leb128.U32Encoding
abbrev CustomsEncoding := CustomsEncodingWith CustomEncoding
abbrev OptionalSectionEncoding {α : Type} := @OptionalSectionEncodingWith α UInt8 Leb128.U32Encoding
abbrev PaddedEncoding {α : Type} := @PaddedEncodingWith α UInt8 CustomEncoding Leb128.U32Encoding
abbrev StartEncoding := StartEncodingWith IndexEncoding

/-- The module header: magic bytes `\0asm` and binary format version 1.
Wasm 2.0 uses this same binary version. -/
def magicVersion : List UInt8 := [0, 0x61, 0x73, 0x6D, 1, 0, 0, 0]

/-- The optional count must match the data section, and every data-indexed body
requires it even when the relevant instruction is nested or unreachable. -/
def DataCountValidWith {ι α : Type} (index : ι → Nat) (count : Option ι) (codes : List α)
    (body : α → List instr) (dataLength : Nat) : Prop :=
  match count with
  | none => ∀ entry ∈ codes, instructionsUseData (body entry) = false
  | some n => index n = dataLength

def DataCountValid (value : Module) : Prop :=
  DataCountValidWith id value.dataCount value.codes Code.body value.data.length

abbrev dataCountSectionId : UInt8 := 12

/-- Data-count occurs before code despite its numerically larger section ID. -/
def DataCountSectionEncoding (value : Option Nat)
    (bytes : List UInt8) : Prop :=
  PaddedEncoding dataCountSectionId StartEncoding none value bytes

/-- The value carried by an optional standard section and its value when absent. -/
structure SectionField (β : Type) where
  {α : Type}
  payload : α → List β → Prop
  absent : α
  value : α

abbrev SectionField.vector {α β : Type} (size : List β → Nat → Prop) (R : α → List β → Prop) (xs : List α) :
    SectionField β := ⟨VecEncodingWith size R, [], xs⟩

abbrev SectionField.index {α β : Type} (R : α → List β → Prop) (value : Option α) : SectionField β :=
  ⟨StartEncodingWith R, none, value⟩

abbrev SectionField.encoding (custom : List β → Prop) (size : List β → Nat → Prop)
    (id : β) (field : SectionField β) : List β → Prop :=
  PaddedEncodingWith custom size id field.payload field.absent field.value

/-- The order, tags, and concatenation of all standard sections, with custom sections at
each boundary. The fields carry payload grammars on the chosen byte representation. -/
def ModuleSectionsWith {β : Type} (byte : UInt8 → β) (custom : List β → Prop)
    (size : List β → Nat → Prop) (types imports functions tables memories globals exports start_
      elements count codes data_ : SectionField β) (countValid : Prop) (bs : List β) : Prop :=
  ∃ ts im fn ta me gl ex st el dc co da trailing,
    types.encoding custom size (byte 1) ts ∧ imports.encoding custom size (byte 2) im ∧
    functions.encoding custom size (byte 3) fn ∧ tables.encoding custom size (byte 4) ta ∧
    memories.encoding custom size (byte 5) me ∧ globals.encoding custom size (byte 6) gl ∧
    exports.encoding custom size (byte 7) ex ∧ start_.encoding custom size (byte 8) st ∧
    elements.encoding custom size (byte 9) el ∧ count.encoding custom size (byte dataCountSectionId) dc ∧
    codes.encoding custom size (byte 10) co ∧ data_.encoding custom size (byte 11) da ∧
    CustomsEncodingWith custom trailing ∧
    bs = magicVersion.map byte ++ ts ++ im ++ fn ++ ta ++ me ++ gl ++ ex ++ st ++ el ++ dc ++ co ++ da ++ trailing ∧
    countValid

/-- The Wasm 2.0 module format, parameterized by the code entry grammar, with custom
sections between the ordered optional sections. Typing checks are separate from this grammar. -/
def ModuleEncodingWith (codeRel : Code → List UInt8 → Prop) (value : Module) (bytes : List UInt8) : Prop :=
  ModuleSectionsWith id CustomEncoding Leb128.U32Encoding
    (.vector Leb128.U32Encoding FuncTypeEncoding value.types) (.vector Leb128.U32Encoding ImportEncoding value.imports)
    (.vector Leb128.U32Encoding IndexEncoding value.functions) (.vector Leb128.U32Encoding TableTypeEncoding value.tables)
    (.vector Leb128.U32Encoding MemTypeEncoding value.memories) (.vector Leb128.U32Encoding GlobalEncoding value.globals)
    (.vector Leb128.U32Encoding ExportEncoding value.exports) (.index IndexEncoding value.start)
    (.vector Leb128.U32Encoding ElementEncoding value.elements) (.index IndexEncoding value.dataCount)
    (.vector Leb128.U32Encoding codeRel value.codes) (.vector Leb128.U32Encoding DataEncoding value.data)
    (DataCountValid value) bytes

/-- A complete body consumes the exact concatenation of token encodings. -/
def BodyBytesWith {τ β : Type} (token : τ → List β → Prop) (emits : List τ → List instr → Prop)
    (ops : List instr) (bytes : List β) : Prop :=
  ∃ tokens, Rep token tokens bytes ∧ emits tokens ops

abbrev BodyBytes := BodyBytesWith TokenEncoding BodyTokens

/-- The size prefix counts exactly the local groups and the instruction body. -/
def CodeEntryWith {α β : Type} (sizeEncoding : List β → Nat → Prop) (localEncoding : α → List β → Prop)
    (bodyEncoding : List instr → List β → Prop) (groups : List α) (ops : List instr) (bytes : List β) : Prop :=
  ∃ size locals body, sizeEncoding size (locals.length + body.length) ∧
    VecEncodingWith sizeEncoding localEncoding groups locals ∧ bodyEncoding ops body ∧ bytes = size ++ locals ++ body

abbrev CodeEncodingWith (bodyRel : List instr → List UInt8 → Prop) (entry : Code) :=
  CodeEntryWith Leb128.U32Encoding LocalEncoding bodyRel entry.locals entry.body

abbrev CodeEncoding := CodeEncodingWith BodyBytes

abbrev ModuleEncoding := ModuleEncodingWith CodeEncoding

end WebAssembly.Binary
