import Itasca.Binary.Wasm1.Encoding

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- Raw declarations retain the original indices and grouped locals. Names
are bytes; their Unicode validity is a separate binary-format judgment. -/
structure Import where
  moduleName : List U8
  «name» : List U8
  desc : module.ImportDesc

structure Export where
  «name» : List U8
  desc : module.ExportDesc

structure Element where
  elem : types.ElemType
  mode : module.ElementMode
  init : List types.ConstExpr

structure Code where
  locals : List (U32 × types.ValueType)
  body : List instr

def Code.declared (entry : Code) : List types.ValueType :=
  entry.locals.flatMap (fun (count, ty) => List.replicate count.val ty)

structure Data where
  mode : module.DataMode
  init : List U8

structure Module where
  types : List types.FuncType
  imports : List Import
  functions : List U32
  tables : List _root_.Itasca.types.TableType
  memories : List _root_.Itasca.types.MemType
  globals : List module.Global
  exports : List Export
  start : Option U32
  elements : List Element
  dataCount : Option U32
  codes : List Code
  data : List Data

/-- Lift an independent encoding to an exact interval of a caller's buffer. -/
def At {α : Type} (R : α → List U8 → Prop) (data : Slice U8)
    (start : Usize) (value : α) (next : Usize) : Prop :=
  ∃ bytes, R value bytes ∧ Wasm1.BytesAt data start bytes next

inductive Rep {α : Type} (R : α → List U8 → Prop) : List α → List U8 → Prop where
  | nil : Rep R [] []
  | cons {value values first rest} : R value first → Rep R values rest →
      Rep R (value :: values) (first ++ rest)

def VecEncoding {α : Type} (R : α → List U8 → Prop) (values : List α)
    (bytes : List U8) : Prop :=
  ∃ count entries, Leb128.Encoding count values.length ∧ Rep R values entries ∧
    bytes = count ++ entries

def IndexEncoding (index : U32) (bytes : List U8) : Prop :=
  Leb128.Encoding bytes index.val

def ByteEncoding (byte : U8) (bytes : List U8) : Prop := bytes = [byte]

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

inductive Utf8 : List U8 → Prop where
  | nil : Utf8 []
  | cons {first rest} : Utf8Char first → Utf8 rest → Utf8 (first ++ rest)

def NameEncoding (nm bytes : List U8) : Prop := ByteVecEncoding nm bytes ∧ Utf8 nm

def valueByte : types.ValueType → U8
  | .I32 => 0x7F#u8 | .I64 => 0x7E#u8 | .F32 => 0x7D#u8 | .F64 => 0x7C#u8
  | .V128 => 0x7B#u8 | .FuncRef => 0x70#u8 | .ExternRef => 0x6F#u8

def elemByte : types.ElemType → U8
  | .FuncRef => 0x70#u8 | .ExternRef => 0x6F#u8

def ValueTypeAllowed (profile : ValidationProfile) (ty : types.ValueType) : Prop :=
  match profile, ty with
  | .Wasm1, .V128 | .Wasm1, .FuncRef | .Wasm1, .ExternRef => False
  | _, _ => True

def ElemTypeAllowed (profile : ValidationProfile) (ty : types.ElemType) : Prop :=
  match profile, ty with
  | .Wasm1, .ExternRef => False
  | _, _ => True

def ValueTypeEncoding (ty : types.ValueType) (bytes : List U8) : Prop :=
  bytes = [valueByte ty]

def ValueTypeEncodingFor (profile : ValidationProfile) (ty : types.ValueType)
    (bytes : List U8) : Prop := ValueTypeEncoding ty bytes ∧ ValueTypeAllowed profile ty

def ElemTypeEncoding (ty : types.ElemType) (bytes : List U8) : Prop := bytes = [elemByte ty]

def ElemTypeEncodingFor (profile : ValidationProfile) (ty : types.ElemType)
    (bytes : List U8) : Prop := ElemTypeEncoding ty bytes ∧ ElemTypeAllowed profile ty

def FuncTypeEncoding (ty : types.FuncType) (bytes : List U8) : Prop :=
  ∃ params results, VecEncoding ValueTypeEncoding ty.params.val params ∧
    VecEncoding ValueTypeEncoding ty.results.val results ∧
    bytes = 0x60#u8 :: (params ++ results)

inductive LimitsEncoding : types.Limits → List U8 → Prop where
  | noMax (min : U32) {bytes} : IndexEncoding min bytes →
      LimitsEncoding ⟨min, none⟩ (0#u8 :: bytes)
  | max (min max : U32) {first rest} : IndexEncoding min first → IndexEncoding max rest →
      LimitsEncoding ⟨min, some max⟩ (1#u8 :: (first ++ rest))

def TableTypeEncoding (ty : types.TableType) (bytes : List U8) : Prop :=
  ∃ limits, LimitsEncoding ty.limits limits ∧ bytes = elemByte ty.elem :: limits

def MemTypeEncoding (ty : types.MemType) (bytes : List U8) : Prop :=
  LimitsEncoding ty.limits bytes

def mutByte : types.Mut → U8 | .Const => 0#u8 | .Var => 1#u8

def GlobalTypeEncoding (ty : types.GlobalType) (bytes : List U8) : Prop :=
  bytes = [valueByte ty.valtype, mutByte ty.mutability]

inductive ConstEncoding : types.ConstExpr → List U8 → Prop where
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
  | refNull (ty : types.ElemType) :
      ConstEncoding (.RefNull ty) [0xD0#u8, elemByte ty, 0x0B#u8]
  | refFunc (index : U32) {bytes} : IndexEncoding index bytes →
      ConstEncoding (.RefFunc index) (0xD2#u8 :: (bytes ++ [0x0B#u8]))
  | v128 (low high : U64) {sub first rest} :
      IndexEncoding 12#u32 sub → FloatBits.Encoding 8 first low.val →
      FloatBits.Encoding 8 rest high.val →
      ConstEncoding (.V128 low high) (0xFD#u8 :: (sub ++ first ++ rest ++ [0x0B#u8]))

def ConstAllowed (profile : ValidationProfile) (expr : types.ConstExpr) : Prop :=
  match profile, expr with
  | .Wasm1, .V128 _ _ | .Wasm1, .RefNull _ | .Wasm1, .RefFunc _ => False
  | _, _ => True

def ConstEncodingFor (profile : ValidationProfile) (expr : types.ConstExpr)
    (bytes : List U8) : Prop := ConstEncoding expr bytes ∧ ConstAllowed profile expr

inductive ImportDescEncoding : module.ImportDesc → List U8 → Prop where
  | func (index : U32) {bytes} : IndexEncoding index bytes →
      ImportDescEncoding (.Func index) (0#u8 :: bytes)
  | table (ty : types.TableType) {bytes} : TableTypeEncoding ty bytes →
      ImportDescEncoding (.Table ty) (1#u8 :: bytes)
  | memory (ty : types.MemType) {bytes} : MemTypeEncoding ty bytes →
      ImportDescEncoding (.Memory ty) (2#u8 :: bytes)
  | global (ty : types.GlobalType) {bytes} : GlobalTypeEncoding ty bytes →
      ImportDescEncoding (.Global ty) (3#u8 :: bytes)

def ImportEncoding (entry : Import) (bytes : List U8) : Prop :=
  ∃ modname nm desc, NameEncoding entry.moduleName modname ∧
    NameEncoding entry.name nm ∧ ImportDescEncoding entry.desc desc ∧
    bytes = modname ++ nm ++ desc

inductive ExportDescEncoding : module.ExportDesc → List U8 → Prop where
  | func (index : U32) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.Func index) (0#u8 :: bytes)
  | table (index : U32) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.Table index) (1#u8 :: bytes)
  | memory (index : U32) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.Memory index) (2#u8 :: bytes)
  | global (index : U32) {bytes} : IndexEncoding index bytes →
      ExportDescEncoding (.Global index) (3#u8 :: bytes)

def ExportEncoding (entry : Export) (bytes : List U8) : Prop :=
  ∃ nm desc, NameEncoding entry.name nm ∧ ExportDescEncoding entry.desc desc ∧
    bytes = nm ++ desc

def GlobalEncoding (entry : module.Global) (bytes : List U8) : Prop :=
  ∃ ty expr, GlobalTypeEncoding entry.gtype ty ∧ ConstEncoding entry.init expr ∧
    bytes = ty ++ expr

/-- The original element format abbreviates each function index as `ref.func`. -/
def ElementEncoding (entry : Element) (bytes : List U8) : Prop :=
  ∃ tableIndex offset initializers table encodedOffset entries,
    entry = ⟨.FuncRef, .Active tableIndex offset, initializers.map types.ConstExpr.RefFunc⟩ ∧
    IndexEncoding tableIndex table ∧ ConstEncoding offset encodedOffset ∧
    VecEncoding IndexEncoding initializers entries ∧ bytes = table ++ encodedOffset ++ entries

/-- Core 2.0's eight element-segment encodings. Flag and index LEBs need not
be minimal; both index vectors and expression vectors retain the same syntax. -/
inductive Wasm2ElementEncoding : Element → List U8 → Prop where
  | activeIndices {offset initializers flags encodedOffset entries} :
      IndexEncoding 0#u32 flags → ConstEncoding offset encodedOffset →
      VecEncoding IndexEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Active 0#u32 offset, initializers.map types.ConstExpr.RefFunc⟩
        (flags ++ encodedOffset ++ entries)
  | passiveIndices {initializers flags entries} :
      IndexEncoding 1#u32 flags → VecEncoding IndexEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Passive, initializers.map types.ConstExpr.RefFunc⟩
        (flags ++ [0#u8] ++ entries)
  | explicitIndices {tableIndex offset initializers flags table encodedOffset entries} :
      IndexEncoding 2#u32 flags → IndexEncoding tableIndex table →
      ConstEncoding offset encodedOffset → VecEncoding IndexEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Active tableIndex offset, initializers.map types.ConstExpr.RefFunc⟩
        (flags ++ table ++ encodedOffset ++ [0#u8] ++ entries)
  | declarativeIndices {initializers flags entries} :
      IndexEncoding 3#u32 flags → VecEncoding IndexEncoding initializers entries →
      Wasm2ElementEncoding ⟨.FuncRef, .Declarative, initializers.map types.ConstExpr.RefFunc⟩
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

/-- The active data-segment flag forms, including nonminimal unsigned LEBs. -/
inductive ActiveIndexEncoding : U32 → Bool → List U8 → Prop where
  | implicit {flags} : IndexEncoding 0#u32 flags → ActiveIndexEncoding 0#u32 false flags
  | explicit {index flags bytes} : IndexEncoding 2#u32 flags → IndexEncoding index bytes →
      ActiveIndexEncoding index true (flags ++ bytes)

def SegmentIndexEncoding (profile : ValidationProfile) (flags index : U32)
    (explicit : Bool) (bytes : List U8) : Prop :=
  match profile with
  | .Wasm1 => index = flags ∧ explicit = false ∧ bytes = []
  | .Wasm2 =>
      (flags = 0#u32 ∧ index = 0#u32 ∧ explicit = false ∧ bytes = []) ∨
      (flags = 2#u32 ∧ explicit = true ∧ IndexEncoding index bytes)

def ElementKindEncoding (explicit : Bool) (bytes : List U8) : Prop :=
  if explicit then bytes = [0#u8] else bytes = []

def ElementEncodingFor (profile : ValidationProfile) (entry : Element)
    (bytes : List U8) : Prop :=
  match profile with
  | .Wasm1 => ElementEncoding entry bytes
  | .Wasm2 => Wasm2ElementEncoding entry bytes

theorem SegmentIndexEncoding.active {flags index explicit bytes headBytes}
    (h : SegmentIndexEncoding .Wasm2 flags index explicit bytes)
    (hf : IndexEncoding flags headBytes) : ActiveIndexEncoding index explicit (headBytes ++ bytes) := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, hi⟩
  · simpa using ActiveIndexEncoding.implicit hf
  · exact .explicit hf hi

theorem ActiveIndexEncoding.parts {index explicit bytes}
    (h : ActiveIndexEncoding index explicit bytes) :
    ∃ flags headBytes suffix, IndexEncoding flags headBytes ∧
      SegmentIndexEncoding .Wasm2 flags index explicit suffix ∧ bytes = headBytes ++ suffix := by
  cases h with
  | implicit hf => exact ⟨0#u32, _, [], hf, Or.inl ⟨rfl, rfl, rfl, rfl⟩, by simp⟩
  | explicit hf hi => exact ⟨2#u32, _, _, hf, Or.inr ⟨rfl, rfl, hi⟩, rfl⟩

/-- Assemble the active index-vector element forms without excluding the other
five Wasm 2.0 segment forms from the independent grammar. -/
theorem ElementEncodingFor.of_parts {profile flags tableIndex explicit offset init fb tb ob kb ib}
    (hf : IndexEncoding flags fb)
    (ht : SegmentIndexEncoding profile flags tableIndex explicit tb)
    (ho : ConstEncoding offset ob) (hk : ElementKindEncoding explicit kb)
    (hi : VecEncoding IndexEncoding init ib) :
    ElementEncodingFor profile
      ⟨.FuncRef, .Active tableIndex offset, init.map types.ConstExpr.RefFunc⟩
      (fb ++ tb ++ ob ++ kb ++ ib) := by
  cases profile with
  | Wasm1 =>
    obtain ⟨rfl, rfl, rfl⟩ := ht
    have hk' : kb = [] := hk
    subst kb
    exact ⟨tableIndex, offset, init, fb, ob, ib, rfl, hf, ho, hi, by simp⟩
  | Wasm2 =>
    rcases ht with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, ht⟩
    · have hk' : kb = [] := hk
      subst kb
      simpa [ElementEncodingFor] using Wasm2ElementEncoding.activeIndices hf ho hi
    · have hk' : kb = [0#u8] := hk
      subst kb
      exact .explicitIndices hf ht ho hi

def LocalEncoding (entry : U32 × types.ValueType) (bytes : List U8) : Prop :=
  ∃ count, IndexEncoding entry.1 count ∧ bytes = count ++ [valueByte entry.2]

/-- Body syntax includes the final end and reconstructs structured instructions.
It imposes no typing or validator acceptance premise. -/
def BodyEncoding (body : List instr) (bytes : List U8) : Prop :=
  ∃ tokens, Rep Wasm1.TokenEncoding tokens bytes ∧ Wasm1.BodyTokens tokens body

def CodeEncoding (entry : Code) (bytes : List U8) : Prop :=
  ∃ size locals body, Leb128.Encoding size (locals.length + body.length) ∧
    VecEncoding LocalEncoding entry.locals locals ∧ BodyEncoding entry.body body ∧
    bytes = size ++ locals ++ body

def DataEncoding (entry : Data) (bytes : List U8) : Prop :=
  ∃ memoryIndex offset memory encodedOffset entries,
    entry.mode = .Active memoryIndex offset ∧ IndexEncoding memoryIndex memory ∧
    ConstEncoding offset encodedOffset ∧ ByteVecEncoding entry.init entries ∧
    bytes = memory ++ encodedOffset ++ entries

inductive Wasm2DataEncoding : Data → List U8 → Prop where
  | active {memoryIndex offset init explicit index encodedOffset entries} :
      ActiveIndexEncoding memoryIndex explicit index → ConstEncoding offset encodedOffset →
      ByteVecEncoding init entries →
      Wasm2DataEncoding ⟨.Active memoryIndex offset, init⟩ (index ++ encodedOffset ++ entries)
  | passive {init flags entries} :
      IndexEncoding 1#u32 flags → ByteVecEncoding init entries →
      Wasm2DataEncoding ⟨.Passive, init⟩ (flags ++ entries)

def DataEncodingFor (profile : ValidationProfile) (entry : Data) (bytes : List U8) : Prop :=
  match profile with
  | .Wasm1 => DataEncoding entry bytes
  | .Wasm2 => Wasm2DataEncoding entry bytes

/-- Section payloads occupy exactly the declared byte count. -/
def SectionEncoding {α : Type} (id : U8) (R : α → List U8 → Prop)
    (value : α) (bytes : List U8) : Prop :=
  ∃ size payload, Leb128.Encoding size payload.length ∧ R value payload ∧
    bytes = id :: (size ++ payload)

def CustomEncoding (bytes : List U8) : Prop :=
  ∃ nm payload encodedName,
    NameEncoding nm encodedName ∧
    SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = encodedName ++ payload) () bytes

inductive CustomsEncoding : List U8 → Prop where
  | nil : CustomsEncoding []
  | cons {first rest} : CustomEncoding first → CustomsEncoding rest →
      CustomsEncoding (first ++ rest)

inductive OptionalSectionEncoding {α : Type} (id : U8) (R : α → List U8 → Prop)
    (absent : α) : α → List U8 → Prop where
  | absent : OptionalSectionEncoding id R absent absent []
  | present {value bytes} : SectionEncoding id R value bytes →
      OptionalSectionEncoding id R absent value bytes

def PaddedEncoding {α : Type} (id : U8) (R : α → List U8 → Prop)
    (absent value : α) (bytes : List U8) : Prop :=
  ∃ customs sec, CustomsEncoding customs ∧
    OptionalSectionEncoding id R absent value sec ∧ bytes = customs ++ sec

/-- Assemble either active data prefix while retaining passive syntax. -/
theorem DataEncodingFor.of_parts {profile flags memoryIndex explicit offset init fb mb ob ib}
    (hf : IndexEncoding flags fb)
    (hm : SegmentIndexEncoding profile flags memoryIndex explicit mb)
    (ho : ConstEncoding offset ob) (hi : ByteVecEncoding init ib) :
    DataEncodingFor profile ⟨.Active memoryIndex offset, init⟩ (fb ++ mb ++ ob ++ ib) := by
  cases profile with
  | Wasm1 =>
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨memoryIndex, offset, fb, ob, ib, rfl, hf, ho, hi, by simp⟩
  | Wasm2 => exact .active (hm.active hf) ho hi

def StartEncoding (value : Option U32) (bytes : List U8) : Prop :=
  ∃ index, value = some index ∧ IndexEncoding index bytes

def magicVersion : List U8 := [0#u8, 0x61#u8, 0x73#u8, 0x6D#u8, 1#u8, 0#u8, 0#u8, 0#u8]

/-- Language restrictions shared by all independent section encodings.
Resource caps and generated typing remain separate. -/
def ModuleTypesAllowed (profile : ValidationProfile) (value : Module) : Prop :=
  (∀ ft ∈ value.types, ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty) ∧
  (∀ entry ∈ value.imports, match entry.desc with
    | .Func _ | .Memory _ => True
    | .Table ty => ElemTypeAllowed profile ty.elem
    | .Global ty => ValueTypeAllowed profile ty.valtype) ∧
  (∀ ty ∈ value.tables, ElemTypeAllowed profile ty.elem) ∧
  (∀ entry ∈ value.globals,
    ValueTypeAllowed profile entry.gtype.valtype ∧ ConstAllowed profile entry.init) ∧
  (∀ entry ∈ value.codes, ∀ decl ∈ entry.locals, ValueTypeAllowed profile decl.2) ∧
  (∀ entry ∈ value.elements, match entry.mode with
    | .Active _ offset => ConstAllowed profile offset
    | _ => True) ∧
  (∀ entry ∈ value.data, match entry.mode with
    | .Active _ offset => ConstAllowed profile offset
    | _ => True)

mutual
  /-- Data indices in instruction syntax trigger the binary data-count requirement. -/
  def instructionUsesData : instr → Bool
    | .MEMORY_INIT _ | .DATA_DROP _ => true
    | .BLOCK _ body | .LOOP _ body => instructionsUseData body
    | .IFELSE _ yes no => instructionsUseData yes || instructionsUseData no
    | _ => false

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
def DataCountSectionEncoding (profile : ValidationProfile) (value : Option U32)
    (bytes : List U8) : Prop :=
  match profile with
  | .Wasm1 => value = none ∧ bytes = []
  | .Wasm2 => PaddedEncoding 12#u8 StartEncoding none value bytes

/-- The complete Wasm 1.0 module format, with custom sections between ordered
optional sections. Semantic checks remain separate from this byte grammar. -/
def ModuleEncodingWith (codeRel : Code → List U8 → Prop) (value : Module) (bytes : List U8)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  ∃ types imports functions tables memories globals exports start elements dataCount codes datas customs,
    PaddedEncoding 1#u8 (VecEncoding FuncTypeEncoding) [] value.types types ∧
    PaddedEncoding 2#u8 (VecEncoding ImportEncoding) [] value.imports imports ∧
    PaddedEncoding 3#u8 (VecEncoding IndexEncoding) [] value.functions functions ∧
    PaddedEncoding 4#u8 (VecEncoding TableTypeEncoding) [] value.tables tables ∧
    PaddedEncoding 5#u8 (VecEncoding MemTypeEncoding) [] value.memories memories ∧
    PaddedEncoding 6#u8 (VecEncoding GlobalEncoding) [] value.globals globals ∧
    PaddedEncoding 7#u8 (VecEncoding ExportEncoding) [] value.exports exports ∧
    PaddedEncoding 8#u8 StartEncoding none value.start start ∧
    PaddedEncoding 9#u8 (VecEncoding (ElementEncodingFor profile)) [] value.elements elements ∧
    DataCountSectionEncoding profile value.dataCount dataCount ∧
    PaddedEncoding 10#u8 (VecEncoding codeRel) [] value.codes codes ∧
    PaddedEncoding 11#u8 (VecEncoding (DataEncodingFor profile)) [] value.data datas ∧
    CustomsEncoding customs ∧
    bytes = magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
      globals ++ exports ++ start ++ elements ++ dataCount ++ codes ++ datas ++ customs ∧
    ModuleTypesAllowed profile value ∧ DataCountValid value

/-- Unbounded syntax; implementation caps are separate completeness premises. -/
def ModuleEncoding : Module → List U8 → Prop := ModuleEncodingWith CodeEncoding

theorem At.span {α : Type} {R : α → List U8 → Prop} {data start value next}
    (h : At R data start value next) : start.val ≤ next.val ∧ next.val ≤ data.length := by
  obtain ⟨bytes, _, hs⟩ := h
  exact ⟨by have := hs.length; omega, hs.bound⟩

theorem Rep.append {α : Type} {R : α → List U8 → Prop} {xs ys bs cs}
    (h : Rep R xs bs) (h' : Rep R ys cs) : Rep R (xs ++ ys) (bs ++ cs) := by
  induction h with
  | nil => simpa using h'
  | cons hx _ ih => simpa [List.append_assoc] using Rep.cons hx ih

theorem Rep.snoc {α : Type} {R : α → List U8 → Prop} {xs x bs last}
    (h : Rep R xs bs) (h' : R x last) : Rep R (xs ++ [x]) (bs ++ last) := by
  simpa using h.append (.cons h' .nil)

theorem Rep.bytes {bytes encoded} (h : Rep ByteEncoding bytes encoded) : encoded = bytes := by
  induction h with
  | nil => rfl
  | cons hb _ ih => simp_all [ByteEncoding]

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
