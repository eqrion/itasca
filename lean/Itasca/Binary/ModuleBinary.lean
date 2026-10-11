import Itasca.Binary.WasmBinaryComplete

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
  tableIdx : U32
  offset : types.ConstExpr
  init : List U32

structure Code where
  locals : List (U32 × types.ValueType)
  body : List instr

def Code.declared (entry : Code) : List types.ValueType :=
  entry.locals.flatMap (fun (count, ty) => List.replicate count.val ty)

structure Data where
  memoryIdx : U32
  offset : types.ConstExpr
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
  codes : List Code
  data : List Data

/-- Lift an independent encoding to an exact interval of a caller's buffer. -/
def At {α : Type} (R : α → List U8 → Prop) (data : Slice U8)
    (start : Usize) (value : α) (next : Usize) : Prop :=
  ∃ bytes, R value bytes ∧ Wasm.BytesAt data start bytes next

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

def ValueTypeEncoding (ty : types.ValueType) (bytes : List U8) : Prop :=
  bytes = [valueByte ty]

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
  ∃ limits, LimitsEncoding ty.limits limits ∧ bytes = 0x70#u8 :: limits

def MemTypeEncoding (ty : types.MemType) (bytes : List U8) : Prop :=
  LimitsEncoding ty.limits bytes

def mutByte : types.Mut → U8 | .Const => 0#u8 | .Var => 1#u8

def GlobalTypeEncoding (ty : types.GlobalType) (bytes : List U8) : Prop :=
  bytes = [valueByte ty.valtype, mutByte ty.mutability]

inductive ConstEncoding : types.ConstExpr → List U8 → Prop where
  | i32 (value : I32) {bytes} : SignedLeb.Encoding bytes value.val →
      ConstEncoding (.I32 value) (0x41#u8 :: (bytes ++ [0x0B#u8]))
  | i64 (value : I64) {bytes} : SignedLeb64.Encoding bytes value.val →
      ConstEncoding (.I64 value) (0x42#u8 :: (bytes ++ [0x0B#u8]))
  | f32 (value : U32) {bytes} : FloatBits.Encoding 4 bytes value.val →
      ConstEncoding (.F32 value) (0x43#u8 :: (bytes ++ [0x0B#u8]))
  | f64 (value : U64) {bytes} : FloatBits.Encoding 8 bytes value.val →
      ConstEncoding (.F64 value) (0x44#u8 :: (bytes ++ [0x0B#u8]))
  | globalGet (index : U32) {bytes} : IndexEncoding index bytes →
      ConstEncoding (.GlobalGet index) (0x23#u8 :: (bytes ++ [0x0B#u8]))

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

def ElementEncoding (entry : Element) (bytes : List U8) : Prop :=
  ∃ table offset entries, IndexEncoding entry.tableIdx table ∧
    ConstEncoding entry.offset offset ∧ VecEncoding IndexEncoding entry.init entries ∧
    bytes = table ++ offset ++ entries

def LocalEncoding (entry : U32 × types.ValueType) (bytes : List U8) : Prop :=
  ∃ count, IndexEncoding entry.1 count ∧ bytes = count ++ [valueByte entry.2]

/-- Body syntax includes the final end and reconstructs structured instructions.
It imposes no typing or validator acceptance premise. -/
def BodyEncoding (body : List instr) (bytes : List U8) : Prop :=
  ∃ tokens, Rep Wasm.TokenEncoding tokens bytes ∧ Wasm.BodyTokens tokens body

def CodeEncoding (entry : Code) (bytes : List U8) : Prop :=
  ∃ size locals body, Leb128.Encoding size (locals.length + body.length) ∧
    VecEncoding LocalEncoding entry.locals locals ∧ BodyEncoding entry.body body ∧
    bytes = size ++ locals ++ body

def DataEncoding (entry : Data) (bytes : List U8) : Prop :=
  ∃ memory offset entries, IndexEncoding entry.memoryIdx memory ∧
    ConstEncoding entry.offset offset ∧ ByteVecEncoding entry.init entries ∧
    bytes = memory ++ offset ++ entries

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

def StartEncoding (value : Option U32) (bytes : List U8) : Prop :=
  ∃ index, value = some index ∧ IndexEncoding index bytes

def magicVersion : List U8 := [0#u8, 0x61#u8, 0x73#u8, 0x6D#u8, 1#u8, 0#u8, 0#u8, 0#u8]

/-- The complete Wasm 1.0 module format, with custom sections between ordered
optional sections. Semantic checks remain separate from this byte grammar. -/
def ModuleEncodingWith (codeRel : Code → List U8 → Prop) (value : Module) (bytes : List U8) : Prop :=
  ∃ types imports functions tables memories globals exports start elements codes datas customs,
    PaddedEncoding 1#u8 (VecEncoding FuncTypeEncoding) [] value.types types ∧
    PaddedEncoding 2#u8 (VecEncoding ImportEncoding) [] value.imports imports ∧
    PaddedEncoding 3#u8 (VecEncoding IndexEncoding) [] value.functions functions ∧
    PaddedEncoding 4#u8 (VecEncoding TableTypeEncoding) [] value.tables tables ∧
    PaddedEncoding 5#u8 (VecEncoding MemTypeEncoding) [] value.memories memories ∧
    PaddedEncoding 6#u8 (VecEncoding GlobalEncoding) [] value.globals globals ∧
    PaddedEncoding 7#u8 (VecEncoding ExportEncoding) [] value.exports exports ∧
    PaddedEncoding 8#u8 StartEncoding none value.start start ∧
    PaddedEncoding 9#u8 (VecEncoding ElementEncoding) [] value.elements elements ∧
    PaddedEncoding 10#u8 (VecEncoding codeRel) [] value.codes codes ∧
    PaddedEncoding 11#u8 (VecEncoding DataEncoding) [] value.data datas ∧
    CustomsEncoding customs ∧
    bytes = magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
      globals ++ exports ++ start ++ elements ++ codes ++ datas ++ customs

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
