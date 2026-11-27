import Aeneas
import Mathlib.Tactic.DSimpPercent
import ItascaRust.Funs
import ItascaRust.Types
import Itasca.Results.Definitions.Foundations
import WebAssembly
import WebAssembly.Binary.Module
import WebAssembly.Binary.Leb128
import WebAssembly.Binary.Opcodes
import WebAssembly.Binary.Memory
import WebAssembly.Binary.DataCount

open WebAssembly

/-!
# Binary reader representations

These predicates describe the byte and syntax witnesses used by the extracted readers.
`WebAssembly.Binary` defines the independent Wasm grammar on `List UInt8`.
Reader contracts specialize the canonical productions to extracted values and bytes,
including nonminimal LEB128 spellings and exact floating-point bits.
-/

/-! ## Binary / BlockTypes -/

section BinaryBlockTypes

/-!
### Value-type and block-type bytes

Independent byte spellings describe value types and the one-byte empty/numeric block cases used by the complete block-type grammar.
-/

/-!
## Value-type byte spellings

`Itasca.Binary.valueByte` supplies literal type bytes used by the independent instruction-immediate grammar.
-/

namespace Itasca.Binary
open Aeneas Aeneas.Std

/-- Preserve all eight bits when exposing extracted reader input to the Wasm grammar. -/
def sourceByte (b : U8) : UInt8 := ⟨b.bv⟩

namespace Source

abbrev bytes (bs : List U8) := bs.map sourceByte

def readerByte (b : UInt8) : U8 := ⟨b.toBitVec⟩
@[simp] theorem readerByte_val (b : UInt8) : (readerByte b).val = b.toNat := rfl

abbrev readerBytes (bs : List UInt8) := bs.map readerByte

@[simp] theorem bytes_readerBytes (bs) : bytes (readerBytes bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => exact congrArg (b :: ·) ih

@[simp] theorem readerBytes_bytes (bs) : readerBytes (bytes bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => exact congrArg (b :: ·) ih

def valueType : wasm_types.ValueType → WebAssembly.Binary.ValueType
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64
  | .V128 => .V128
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

def readerValueType : WebAssembly.Binary.ValueType → wasm_types.ValueType
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64
  | .V128 => .V128
  | .FUNCREF => .FuncRef
  | .EXTERNREF => .ExternRef

end Source

/-- The canonical value-type byte in the extracted reader's representation. -/
def valueByte (ty : wasm_types.ValueType) : U8 :=
  Source.readerByte (WebAssembly.Binary.valueByte (Source.valueType ty))

end Itasca.Binary

/-!
## Numeric and empty block bytes

`ScalarBlockByte` gives the one-byte empty/numeric cases used within the complete
block-type grammar. It is an internal grammar decomposition, not a language mode.
-/

namespace Itasca.Body.Scalar
open Aeneas Aeneas.Std

/-- The one-byte spelling of an empty block type or a numeric result type. -/
abbrev ScalarBlockByte := WebAssembly.Binary.ScalarBlockByteWith signature.BlockType.Empty
  (fun ty => signature.BlockType.Value (Binary.Source.readerValueType ty)) Binary.Source.readerByte

end Itasca.Body.Scalar

end BinaryBlockTypes

/-! ## Binary / Body / Syntax -/

section BinaryBodySyntax

/-!
### Flat and structured instructions

`Token`, `Simple`, `Emits` and `BodyTokens` relate flat headers/end markers to structured specification instructions.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

abbrev Token := WebAssembly.Binary.TokenWith signature.BlockType
abbrev Simple := @WebAssembly.Binary.SimpleWith signature.BlockType
abbrev Emits := WebAssembly.Binary.EmitsWith blockType
abbrev BodyTokens := WebAssembly.Binary.BodyTokensWith blockType

end Itasca.Body

end BinaryBodySyntax

/-! ## Binary / Leb128 -/

section BinaryLeb128

/-!
### Unsigned LEB encodings and reader spans

`Encoding` relates bytes to values; `Decoded` also fixes the input slice and cursor endpoints.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.Leb128

/-- Little-endian base-128 payload, independent of the implementation's scalars. -/
def payload := WebAssembly.Binary.Leb128.payloadWith (@UScalar.val .U8)

theorem payload_nil : payload [] = 0 := rfl
theorem payload_cons (b : U8) (bs) : payload (b :: bs) = b.val % 128 + 128 * payload bs := rfl

attribute [eqns payload_nil payload_cons] payload

/-- An unsigned 32-bit binary encoding on the reader's bytes. -/
def Encoding := WebAssembly.Binary.Leb128.UnsignedForm (@UScalar.val .U8) payload

/-- A successful decoding identifies both the consumed bytes and the untouched suffix. -/
def Decoded (data : Slice U8) (start : Usize) (value : U32) (next : Usize) : Prop :=
  ∃ bytes, data.val.drop start.val = bytes ++ data.val.drop next.val ∧
    next.val = start.val + bytes.length ∧ next.val ≤ data.length ∧
    Encoding bytes value.val

end Itasca.Binary.Leb128

end BinaryLeb128

/-! ## Binary / SignedLeb -/

section BinarySignedLeb

/-!
### Shared signed LEB encodings

Decoder-format bounds, terminal signed values and encoding predicates describe signed LEB
bytes. The 33-bit specialization retains the block-signature representation.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.SignedLeb

/-- Parameters of the shared `I128` signed decoder: the index of the last permitted byte and the
inclusive value range. The bound `last ≤ 9` keeps every intermediate operation within `I128`. -/
structure Format where
  last : U32
  lower : I128
  upper : I128
  last_le : last.val ≤ 9

/-- The contribution of the terminating signed byte, including sign extension. -/
def finalValue (acc mult : Int) (last : U8) : Int :=
  dsimp% only [WebAssembly.Binary.Leb128.signedFinal] WebAssembly.Binary.Leb128.signedFinal acc mult last.val

/-- Instantiate the binary grammar with the reader's scalar bounds. -/
def Encoding (format : Format) := WebAssembly.Binary.Leb128.SignedForm
  (@UScalar.val .U8) Binary.Leb128.payload finalValue format.last.val format.lower.val format.upper.val

end Itasca.Binary.SignedLeb

namespace Itasca.Binary.SignedLeb33

/-- The signed 33-bit specialization of the shared decoder proof. -/
def format : Binary.SignedLeb.Format := ⟨4#u32, (-4294967296)#i128, 4294967295#i128, by decide⟩

/-- Signed 33-bit LEB128 bytes, permitting nonminimal sign extension. -/
abbrev Encoding := Binary.SignedLeb.Encoding format

end Itasca.Binary.SignedLeb33

end BinarySignedLeb

/-! ## Binary / ScalarEncoding -/

section BinaryScalarEncoding

/-!
### Fixed-width bits and signed integer encodings

Little-endian float-bit payloads and signed 32/64-bit LEB predicates describe scalar
immediates independently of the reader. Permitted nonminimal sign extension remains
represented.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.FloatBits

/-- Little-endian value of a byte list, using every bit of each byte. -/
def payload := WebAssembly.Binary.FloatBits.payloadWith (@UScalar.val .U8)

theorem payload_nil : payload [] = 0 := rfl
theorem payload_cons (b : U8) (bs) : payload (b :: bs) = b.val + 256 * payload bs := rfl

attribute [eqns payload_nil payload_cons] payload

/-- Exactly `n` bytes whose little-endian value is the bit pattern. -/
abbrev Encoding := WebAssembly.Binary.FloatBits.EncodingForm payload

end Itasca.Binary.FloatBits

namespace Itasca.Binary.SignedLeb32

/-- The signed 32-bit specialization of the shared decoder proof. -/
def format : Binary.SignedLeb.Format := ⟨4#u32, (-2147483648)#i128, 2147483647#i128, by decide⟩

/-- Signed 32-bit LEB128 bytes, permitting nonminimal sign extension. -/
abbrev Encoding := Binary.SignedLeb.Encoding format

end Itasca.Binary.SignedLeb32

namespace Itasca.Binary.SignedLeb64

/-- The signed 64-bit specialization of the shared decoder proof. -/
def format : Binary.SignedLeb.Format := ⟨9#u32, (-9223372036854775808)#i128, 9223372036854775807#i128, by decide⟩

/-- Signed 64-bit LEB128 bytes, permitting nonminimal sign extension. -/
abbrev Encoding := Binary.SignedLeb.Encoding format

end Itasca.Binary.SignedLeb64

end BinaryScalarEncoding

/-! ## Spec / Constants -/

section SpecConstants

/-!
### Scalar literal meanings

Integer and floating-point constant constructors preserve the source values represented by concrete literal bits.
-/

open Aeneas Aeneas.Std

namespace Itasca.Spec

/-- The SpecTec `i32.const` instruction for `value`, using its unsigned 32-bit bit pattern. -/
def i32Const (value : I32) : instr :=
  dsimp% only [WebAssembly.Binary.Constants.i32Const] WebAssembly.Binary.Constants.i32Const value.val

end Itasca.Spec

namespace Itasca.Spec.Constants

/-- The SpecTec `i64.const` instruction for `value`, using its unsigned 64-bit bit pattern. -/
def i64 (value : I64) : instr :=
  dsimp% only [WebAssembly.Binary.Constants.i64] WebAssembly.Binary.Constants.i64 value.val

export WebAssembly.Binary.Constants (floatValue)

/-- The SpecTec `f32.const` instruction for the bit pattern `bits`. -/
def f32 (bits : U32) : instr :=
  dsimp% only [WebAssembly.Binary.Constants.f32] WebAssembly.Binary.Constants.f32 bits.val

/-- The SpecTec `f64.const` instruction for the bit pattern `bits`. -/
def f64 (bits : U64) : instr :=
  dsimp% only [WebAssembly.Binary.Constants.f64] WebAssembly.Binary.Constants.f64 bits.val

end Itasca.Spec.Constants

end SpecConstants

/-! ## Binary / ScalarInstructions -/

section BinaryScalarInstructions

/-!
### Scalar instruction bytes

Numeric/memory opcode meanings, exact byte spans and scalar immediate relations form an internal component of the complete instruction grammar.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.MemoryMeaning

/-- The SpecTec memory argument of a Rust `MemArg`. -/
def memArg (arg : code.MemArg) : memarg :=
  { ALIGN := .mk_uN arg.align.val, OFFSET := .mk_uN arg.offset.val }

/-- A row of the memory opcode table: the value type, the natural alignment exponent, whether it is
a store, and the instruction built from a memory argument. -/
structure Operation where
  ty : wasm_types.ValueType
  naturalAlign : U32
  store : Bool
  op : code.MemArg → instr

/-- A load of the full width of a number type. -/
def fullLoad (ty : wasm_types.ValueType) (nt : numtype) (alignment : U32) : Operation :=
  ⟨ty, alignment, false, fun arg => .LOAD nt none (memArg arg)⟩

/-- A packed integer load of the given bit width and signedness. -/
def packedLoad (ty : wasm_types.ValueType) (it : Inn) (width : Nat)
    (extension : sx) (alignment : U32) : Operation :=
  ⟨ty, alignment, false, fun arg =>
    .LOAD (numtype_Inn it) (some (.mk_loadop__0 it (.mk_loadop_Inn (.mk_sz width) extension))) (memArg arg)⟩

/-- A store of the full width of a number type. -/
def fullStore (ty : wasm_types.ValueType) (nt : numtype) (alignment : U32) : Operation :=
  ⟨ty, alignment, true, fun arg => .STORE nt none (memArg arg)⟩

/-- A packed integer store of the given bit width. -/
def packedStore (ty : wasm_types.ValueType) (it : Inn) (width : Nat) (alignment : U32) : Operation :=
  ⟨ty, alignment, true, fun arg => .STORE (numtype_Inn it) (some (.mk_sz width)) (memArg arg)⟩

/-- Convert the operand type in a memory opcode row to the reader's representation. -/
abbrev readerType := Binary.Source.readerValueType

/-- Instantiate the Wasm memory opcode table with the validator's operation descriptors. -/
def opcodeMeaning (opcode : U8) : Option Operation :=
  dsimp% only [WebAssembly.Binary.MemoryMeaning.opcodeTable, readerType]
    WebAssembly.Binary.MemoryMeaning.opcodeTable opcode.val
      (fun t nt a => fullLoad (readerType t) nt ⟨BitVec.ofNat 32 a⟩)
      (fun t it w sx a => packedLoad (readerType t) it w sx ⟨BitVec.ofNat 32 a⟩)
      (fun t nt a => fullStore (readerType t) nt ⟨BitVec.ofNat 32 a⟩)
      (fun t it w a => packedStore (readerType t) it w ⟨BitVec.ofNat 32 a⟩)

end Itasca.Body.MemoryMeaning

namespace Itasca.Body.Numeric

/-- Scalar numeric bytes select a SpecTec instruction directly. Stack effects
and well-formedness are proved about this independent table in Binary; neither
is a premise of decoding. -/
def opcodeInstruction (opcode : U8) : Option instr :=
  dsimp% only [WebAssembly.Binary.Numeric.opcodeInstruction] WebAssembly.Binary.Numeric.opcodeInstruction ⟨opcode.bv⟩

end Itasca.Body.Numeric

namespace Itasca.Body.Scalar

export Body (Token Simple Emits BodyTokens)

/-- `bytes` is the slice of `data` from `start` to `next`, followed by the untouched suffix. -/
structure BytesAt (data : Slice U8) (start : Usize) (bytes : List U8) (next : Usize) : Prop where
  suffix : data.val.drop start.val = bytes ++ data.val.drop next.val
  length : next.val = start.val + bytes.length
  bound : next.val ≤ data.length

/-- The concatenated unsigned LEB128 entries of an index vector, without the leading count. -/
abbrev operands : WebAssembly.Binary.Scalar.Operands U8 U32 I32 I64 U64 code.MemArg Body.MemoryMeaning.Operation signature.BlockType where
  byte := Binary.Source.readerByte
  index := UScalar.val
  int32 := IScalar.val
  int64 := IScalar.val
  word64 := UScalar.val
  align := fun a => a.align.val
  offset := fun a => a.offset.val
  memory := Body.MemoryMeaning.opcodeMeaning
  instruction := Body.MemoryMeaning.Operation.op
  numeric := Body.Numeric.opcodeInstruction
  blockByte := ScalarBlockByte
  leb := Binary.Leb128.Encoding
  s32 := Binary.SignedLeb32.Encoding
  s64 := Binary.SignedLeb64.Encoding
  float := Binary.FloatBits.Encoding

abbrev IndicesEncoding := WebAssembly.Binary.Scalar.IndicesEncodingWith (@UScalar.val .U32) Binary.Leb128.Encoding
abbrev Immediate := WebAssembly.Binary.Scalar.ImmediateWith operands

end Itasca.Body.Scalar

end BinaryScalarInstructions

/-! ## Spec / DeclaredReferences -/

section SpecDeclaredReferences

/-!
### Declared function-reference restrictions

Instruction and module predicates collect the additional ref.func declaration condition
absent from the pinned generated typing rules. Calls and declaration sites remain distinct
from references requiring declarations.
-/

open Aeneas Aeneas.Std

namespace Itasca.Spec.DeclaredReferences

mutual
  /-- Function-index occurrences in an instruction tree. With `calls = false`,
  collect only the occurrences whose typing requires a reference declaration. -/
  def instructionIndices (calls : Bool) : instr → List funcidx
    | .CALL x => if calls then [x] else []
    | .REF_FUNC x => [x]
    | .BLOCK _ body | .LOOP _ body => instructionsIndices calls body
    | .IFELSE _ yes no => instructionsIndices calls yes ++ instructionsIndices calls no
    | _ => []

  /-- Function-index occurrences in a sequence, including nested control bodies. -/
  def instructionsIndices (calls : Bool) : List instr → List funcidx
    | [] => []
    | op :: ops => instructionIndices calls op ++ instructionsIndices calls ops
end

end Itasca.Spec.DeclaredReferences

namespace Itasca.Spec.DeclaredReferences

/-- All `ref.func` occurrences in a sequence have declarations in `refs`. -/
def Instructions (refs : List funcidx) (ops : List instr) : Prop :=
  ∀ x ∈ instructionsIndices false ops, x ∈ refs

/-- Function indices occurring in a global initializer. -/
def globalIndices : global → List funcidx
  | .GLOBAL _ body => instructionsIndices true body

/-- Function indices occurring in an active element's offset expression. -/
def elementModeIndices : elemmode → List funcidx
  | .ACTIVE _ offset => instructionsIndices true offset
  | .PASSIVE | .DECLARE => []

/-- Function indices in an element segment's initializers and mode. -/
def elementIndices : elem → List funcidx
  | .ELEM _ initializers mode =>
    initializers.flatMap (instructionsIndices true) ++ elementModeIndices mode

/-- Function indices in an active data segment's offset expression. -/
def dataIndices : data → List funcidx
  | .DATA _ (.ACTIVE _ offset) => instructionsIndices true offset
  | .DATA _ .PASSIVE => []

/-- The function index of an exported function; other exports contribute none. -/
def exportIndices : «export» → List funcidx
  | .EXPORT _ (.FUNC x) => [x]
  | _ => []

/-- The declared references of a module: Core 2.0's `funcidx(module with funcs = [] with start =
none)`. Types, imports, tables and memories contain no function indices in Core 2.0. -/
def declarations : WebAssembly.module → List funcidx
  | .MODULE _ _ _ globals _ _ elements datas _ exports =>
    globals.flatMap globalIndices ++ elements.flatMap elementIndices ++
      datas.flatMap dataIndices ++ exports.flatMap exportIndices

/-- The declared-reference obligation on one function's complete instruction tree. -/
def Function (refs : List funcidx) : func → Prop
  | .FUNC _ _ body => Instructions refs body

/-- The reference-declaration condition missing from the generated specification. Occurrences
outside function bodies already belong to `declarations`, so only function bodies need a
membership check. The start index is neither a declaration nor a use of `ref.func`. -/
def Module (m : WebAssembly.module) : Prop :=
  match m with
  | .MODULE _ _ funcs _ _ _ _ _ _ _ =>
    ∀ f ∈ funcs, Function (declarations m) f

end Itasca.Spec.DeclaredReferences

end SpecDeclaredReferences

/-! ## Binary / Body / OpcodeMeaning -/

section BinaryBodyOpcodeMeaning

/-!
### Instruction-family meanings

Bulk and reference immediates, numeric extensions, and SIMD lane/memory
descriptors supply independent source instructions for body validation.
Literal opcode tables retain operand/result types and immediate bounds.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.BulkBinary

/-- The immediates of bulk memory and table instructions after their `0xfc` subopcode. Memory
indices are reserved literal zero bytes. -/
abbrev Immediate := WebAssembly.Binary.BulkBinary.ImmediateWith (@UScalar.val .U32)
  (fun n => (⟨n.toBitVec⟩ : U32)) Binary.Source.readerByte Binary.Leb128.Encoding

end Itasca.Body.BulkBinary

namespace Itasca.Body.NumericExtensions

/-- Independent sign opcode mapping into SpecTec syntax. -/
def signInstruction (opcode : U8) : Option instr :=
  dsimp% only [WebAssembly.Binary.NumericExtensions.signInstruction] WebAssembly.Binary.NumericExtensions.signInstruction ⟨opcode.bv⟩

def saturatingInstruction (opcode : U32) : Option instr :=
  dsimp% only [WebAssembly.Binary.NumericExtensions.saturatingInstruction] WebAssembly.Binary.NumericExtensions.saturatingInstruction opcode.val

end Itasca.Body.NumericExtensions

namespace Itasca.Body.ReferencesBinary

/-- The reference type tag is the literal byte `0x70` or `0x6f`. -/
def referenceByte (ty : wasm_types.ElemType) : U8 :=
  Binary.Source.readerByte (WebAssembly.Binary.ReferencesBinary.referenceByte (Translation.referenceType ty))

/-- The immediates of reference, typed select, table access and indirect call instructions. Index
encodings admit every valid unsigned LEB128. -/
abbrev Immediate := WebAssembly.Binary.ReferencesBinary.ImmediateWith Binary.Source.readerByte
  (@UScalar.val .U32) Translation.referenceType Translation.valueType Binary.valueByte Binary.Leb128.Encoding

end Itasca.Body.ReferencesBinary

namespace Itasca.Body.Simd

abbrev LaneOperation := WebAssembly.Binary.Simd.LaneOperation
abbrev MemoryOperation := WebAssembly.Binary.Simd.MemoryOperation

namespace LaneOperation
abbrev shape (op : LaneOperation) :=
  dsimp% only [WebAssembly.Binary.Simd.LaneOperation.shape] WebAssembly.Binary.Simd.LaneOperation.shape op
abbrev replace (op : LaneOperation) :=
  dsimp% only [WebAssembly.Binary.Simd.LaneOperation.replace] WebAssembly.Binary.Simd.LaneOperation.replace op
abbrev extension (op : LaneOperation) :=
  dsimp% only [WebAssembly.Binary.Simd.LaneOperation.extension] WebAssembly.Binary.Simd.LaneOperation.extension op
abbrev instruction (op : LaneOperation) (lane : laneidx) :=
  dsimp% only [WebAssembly.Binary.Simd.LaneOperation.instruction] WebAssembly.Binary.Simd.LaneOperation.instruction op lane
end LaneOperation

namespace MemoryOperation
abbrev laneCount (op : MemoryOperation) :=
  dsimp% only [WebAssembly.Binary.Simd.MemoryOperation.laneCount] WebAssembly.Binary.Simd.MemoryOperation.laneCount op
abbrev instruction (op : MemoryOperation) (arg : memarg) (lane : laneidx) :=
  dsimp% only [WebAssembly.Binary.Simd.MemoryOperation.instruction] WebAssembly.Binary.Simd.MemoryOperation.instruction op arg lane
end MemoryOperation

abbrev laneMeaning (opcode : Nat) : Option LaneOperation :=
  dsimp% only [WebAssembly.Binary.Simd.laneMeaning] WebAssembly.Binary.Simd.laneMeaning opcode
abbrev memoryMeaning (opcode : Nat) : Option MemoryOperation :=
  dsimp% only [WebAssembly.Binary.Simd.memoryMeaning] WebAssembly.Binary.Simd.memoryMeaning opcode

end Itasca.Body.Simd

end BinaryBodyOpcodeMeaning

/-! ## Binary / Body / SimdPureMeaning -/

section BinaryBodySimdPureMeaning

/-!
### Pure SIMD binary syntax

This table maps decimal SIMD subopcodes directly to SpecTec instructions.
It specifies the binary format independently of validator dispatch. Typing,
stack effects and well-formedness are properties proved about this mapping;
none is an input to the grammar. Unlisted subopcodes have no pure encoding.
-/

namespace Itasca.Body.Simd

export WebAssembly.Binary.Simd (pureInstruction)

end Itasca.Body.Simd

end BinaryBodySimdPureMeaning

/-! ## Binary / Body / Encoding -/

section BinaryBodyEncoding

/-!
### Complete instruction bytes

Immediate, block, token and consumed-span relations combine scalar, reference, bulk, numeric-extension and SIMD encodings into the body grammar.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

/-- A `v128.const` of 128 immediate bits, given as two little-endian 64-bit halves. -/
def vectorConstant (low high : U64) :=
  dsimp% only [WebAssembly.Binary.Simd.vectorConstant] WebAssembly.Binary.Simd.vectorConstant low.val high.val

export WebAssembly.Binary.Simd (unpackBytes)

def shuffleIndices (low high : U64) :=
  dsimp% only [WebAssembly.Binary.Simd.shuffleIndices] WebAssembly.Binary.Simd.shuffleIndices low.val high.val

def shuffle (low high : U64) :=
  dsimp% only [WebAssembly.Binary.Simd.shuffle] WebAssembly.Binary.Simd.shuffle low.val high.val

abbrev operands : WebAssembly.Binary.Simd.Operands U8 U32 code.MemArg U64 :=
  ⟨UScalar.val, fun n => ⟨n.toBitVec⟩, UScalar.val, fun a => a.align.val, fun a => a.offset.val,
    UScalar.val, Binary.Leb128.Encoding, Binary.FloatBits.Encoding 8⟩

abbrev Immediate := WebAssembly.Binary.Simd.ImmediateWith operands

end Itasca.Body.Simd

namespace Itasca.Body

/-- A block type as a literal tag byte or a nonnegative signed 33-bit type index. -/
abbrev BlockEncoding (bt : signature.BlockType) (bs : List U8) :=
  WebAssembly.Binary.BlockEncoding (blockType bt) (Binary.Source.bytes bs)

/-- The immediate bytes that follow an opcode byte for a Wasm 2.0 token. Plain scalar leaves are
reused, but structured instructions take `BlockEncoding` block types. -/
abbrev instructionOperands : WebAssembly.Binary.InstructionOperands U8 U32 signature.BlockType :=
  ⟨Binary.Source.readerByte, UScalar.val, fun oc op => Scalar.Immediate oc (.plain op),
    NumericExtensions.signInstruction, NumericExtensions.saturatingInstruction,
    ReferencesBinary.Immediate, BulkBinary.Immediate, Simd.Immediate, BlockEncoding, Binary.Leb128.Encoding⟩

abbrev Immediate := WebAssembly.Binary.ImmediateWith instructionOperands
abbrev TokenEncoding := WebAssembly.Binary.TokenEncodingWith Immediate

/-- A token is encoded by the interval from `start` to `next`. The suffix is unrestricted. -/
def At (data : Slice U8) (start : Usize) (token : Token) (next : Usize) : Prop :=
  ∃ bytes, TokenEncoding token bytes ∧ Body.Scalar.BytesAt data start bytes next

/-- The tokens read from `start` to the cursor, accumulated one `At` step at a time. Unread bytes
are unconstrained. -/
inductive Consumed (data : Slice U8) : Usize → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Consumed data pos [] pos
  | snoc {start tokens pos token next} : Consumed data start tokens pos →
      At data pos token next → Consumed data start (tokens ++ [token]) next

/-- A complete function body: the tokens read from offset 0 reach the end of `data`, and end with
the final `end`. -/
def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  ∃ tokens next, Consumed data 0#usize tokens next ∧
    next.val = data.length ∧ BodyTokens tokens ops

end Itasca.Body

end BinaryBodyEncoding

/-! ## Binary / ModuleGrammar -/

section BinaryModuleGrammar

/-!
### Independent module grammar

Raw modules, exact byte spans, vectors, Unicode names, constants, segments and section framing define decoding independently of validator acceptance.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

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
  ∃ bytes, R value bytes ∧ Body.Scalar.BytesAt data start bytes next

abbrev Rep {α : Type} := @WebAssembly.Binary.Rep α U8

abbrev VecEncoding {α : Type} := @WebAssembly.Binary.VecEncodingWith α U8 Leb128.Encoding

/-- An index as an unsigned LEB128 `u32`. -/
def IndexEncoding (index : U32) (bytes : List U8) : Prop :=
  Binary.Leb128.Encoding bytes index.val

/-- A single raw byte. -/
abbrev ByteEncoding := @WebAssembly.Binary.ByteEncoding U8

/-- A vector of raw bytes. -/
abbrev ByteVecEncoding := WebAssembly.Binary.ByteVecEncodingWith Leb128.Encoding

abbrev Utf8Char := WebAssembly.Binary.Utf8CharWith (@UScalar.val .U8)
abbrev Utf8 := WebAssembly.Binary.Utf8With (@UScalar.val .U8)

/-- A name: a byte vector whose contents are valid UTF-8. -/
abbrev NameEncoding := WebAssembly.Binary.NameEncodingWith (@UScalar.val .U8) Leb128.Encoding

/-- The binary type byte of a reference element type. -/
abbrev elemByte := Itasca.Body.ReferencesBinary.referenceByte

abbrev ValueTypeEncoding (ty : wasm_types.ValueType) (bs : List U8) :=
  WebAssembly.Binary.ValueTypeEncoding (Translation.valueType ty) (Source.bytes bs)

theorem ValueTypeEncoding.reader_bytes {ty bs} :
    ValueTypeEncoding ty bs ↔ bs = [Itasca.Binary.valueByte ty] := by
  constructor
  · rintro ⟨v, hv, hb⟩
    have eq : Source.valueType ty = v := by
      cases ty <;> cases v <;> first | rfl | contradiction
    subst v
    have he := congrArg Source.readerBytes hb
    rw [Source.readerBytes_bytes] at he
    exact he
  · rintro rfl
    exact ⟨Source.valueType ty, by cases ty <;> rfl, rfl⟩

abbrev FuncTypeEncoding (ty : wasm_types.FuncType) (bs : List U8) :=
  WebAssembly.Binary.FuncTypeEncoding (Translation.Environment.funcType ty) (Source.bytes bs)

abbrev LimitsEncoding (lim : wasm_types.Limits) (bs : List U8) :=
  WebAssembly.Binary.LimitsEncoding (Translation.Environment.limitsType lim) (Source.bytes bs)

abbrev TableTypeEncoding (ty : wasm_types.TableType) (bs : List U8) :=
  WebAssembly.Binary.TableTypeEncoding (Translation.Environment.tableType ty) (Source.bytes bs)

abbrev MemTypeEncoding (ty : wasm_types.MemType) (bs : List U8) :=
  WebAssembly.Binary.MemTypeEncoding (Translation.Environment.memType ty) (Source.bytes bs)

/-- The binary mutability byte. -/
def mutByte (m : wasm_types.Mut) : U8 :=
  Source.readerByte (WebAssembly.Binary.mutabilityByte (Translation.mutability m))

@[simp] theorem mutByte_const : mutByte .Const = 0#u8 := rfl
@[simp] theorem mutByte_var : mutByte .Var = 1#u8 := rfl

/-- A global type: the value type byte followed by the mutability byte. -/
abbrev GlobalTypeEncoding (ty : wasm_types.GlobalType) (bs : List U8) :=
  WebAssembly.Binary.GlobalTypeEncoding (Translation.globalType ty) (Source.bytes bs)

namespace Source

def constant : wasm_types.ConstExpr → WebAssembly.Binary.ConstExpr
  | .I32 v => .I32 v.val
  | .I64 v => .I64 v.val
  | .F32 v => .F32 v.val
  | .F64 v => .F64 v.val
  | .V128 lo hi => .V128 lo.val hi.val
  | .GlobalGet i => .GlobalGet i.val
  | .RefNull t => .RefNull (Translation.referenceType t)
  | .RefFunc i => .RefFunc i.val

end Source

abbrev ConstEncoding (e : wasm_types.ConstExpr) (bs : List U8) :=
  WebAssembly.Binary.ConstEncoding (Source.constant e) (Source.bytes bs)

namespace Source

def importDesc : metadata.ImportDesc → WebAssembly.Binary.ImportDesc
  | .Func i => .Func i.val
  | .Table t => .Table (Translation.Environment.tableType t)
  | .Memory t => .Memory (Translation.Environment.memType t)
  | .Global t => .Global (Translation.globalType t)

def exportDesc : metadata.ExportDesc → externidx
  | .Func i => .FUNC (.mk_uN i.val)
  | .Table i => .TABLE (.mk_uN i.val)
  | .Memory i => .MEM (.mk_uN i.val)
  | .Global i => .GLOBAL (.mk_uN i.val)

def importEntry (e : Itasca.Binary.Import) : WebAssembly.Binary.Import :=
  ⟨bytes e.moduleName, bytes e.name, importDesc e.desc⟩

def globalEntry (e : metadata.Global) : WebAssembly.Binary.Global :=
  ⟨Translation.globalType e.gtype, constant e.init⟩

def exportEntry (e : Itasca.Binary.Export) : WebAssembly.Binary.Export :=
  ⟨bytes e.name, exportDesc e.desc⟩

end Source

abbrev ImportDescEncoding (d : metadata.ImportDesc) (bs : List U8) :=
  WebAssembly.Binary.ImportDescEncoding (Source.importDesc d) (Source.bytes bs)

/-- An import: module name, field name and descriptor. -/
abbrev ImportEncoding (entry : Import) (bs : List U8) :=
  WebAssembly.Binary.ImportEncoding (Source.importEntry entry) (Source.bytes bs)

abbrev ExportDescEncoding (d : metadata.ExportDesc) (bs : List U8) :=
  WebAssembly.Binary.ExportDescEncoding (Source.exportDesc d) (Source.bytes bs)

/-- An export: name and descriptor. -/
abbrev ExportEncoding (entry : Export) (bs : List U8) :=
  WebAssembly.Binary.ExportEncoding (Source.exportEntry entry) (Source.bytes bs)

/-- A global: its type followed by its initializer expression. -/
abbrev GlobalEncoding (entry : metadata.Global) (bs : List U8) :=
  WebAssembly.Binary.GlobalEncoding (Source.globalEntry entry) (Source.bytes bs)

namespace Source

def elementMode : metadata.ElementMode → WebAssembly.Binary.ElementMode
  | .Active i e => .Active i.val (constant e)
  | .Passive => .Passive
  | .Declarative => .Declarative


def element (e : Itasca.Binary.Element) : WebAssembly.Binary.Element :=
  ⟨Translation.referenceType e.elem, elementMode e.mode,
    e.init.map constant⟩

end Source

abbrev ElementEncoding (e : Element) (bs : List U8) :=
  WebAssembly.Binary.ElementEncoding (Source.element e) (Source.bytes bs)

/-- The active segment flag forms of a data segment, including non-minimal unsigned LEBs. -/
abbrev ActiveIndexEncoding (i : U32) (explicit : Bool) (bs : List U8) :=
  WebAssembly.Binary.ActiveIndexEncoding i.val explicit (Source.bytes bs)

namespace Source

def localDecl (e : U32 × wasm_types.ValueType) := (e.1.val, valueType e.2)

end Source

abbrev LocalEncoding (entry : U32 × wasm_types.ValueType) (bs : List U8) :=
  WebAssembly.Binary.LocalEncoding (Source.localDecl entry) (Source.bytes bs)

namespace Source

def dataMode : metadata.DataMode → WebAssembly.Binary.DataMode
  | .Active i e => .Active i.val (constant e)
  | .Passive => .Passive

def dataEntry (e : Itasca.Binary.Data) : WebAssembly.Binary.Data :=
  ⟨dataMode e.mode, bytes e.init⟩

end Source

abbrev DataEncoding (d : Data) (bs : List U8) :=
  WebAssembly.Binary.DataEncoding (Source.dataEntry d) (Source.bytes bs)

abbrev SectionEncoding {α : Type} := @WebAssembly.Binary.SectionEncodingWith α U8 Leb128.Encoding
abbrev CustomEncoding := WebAssembly.Binary.CustomEncodingWith (@UScalar.val .U8) Source.readerByte Leb128.Encoding
abbrev CustomsEncoding := WebAssembly.Binary.CustomsEncodingWith CustomEncoding
abbrev OptionalSectionEncoding {α : Type} := @WebAssembly.Binary.OptionalSectionEncodingWith α U8 Leb128.Encoding
abbrev PaddedEncoding {α : Type} := @WebAssembly.Binary.PaddedEncodingWith α U8 CustomEncoding Leb128.Encoding
abbrev StartEncoding := WebAssembly.Binary.StartEncodingWith IndexEncoding

/-- The module header: magic bytes `\0asm` and binary format version 1.
Wasm 2.0 uses this same binary version. -/
def magicVersion : List U8 :=
  dsimp% only [Source.readerBytes, WebAssembly.Binary.magicVersion, List.map] (Source.readerBytes WebAssembly.Binary.magicVersion)

export WebAssembly.Binary (instructionUsesData instructionsUseData)

/-- The optional count must match the data section, and every data-indexed body
requires it even when the relevant instruction is nested or unreachable. -/
def DataCountValid (value : Module) : Prop :=
  WebAssembly.Binary.DataCountValidWith (@UScalar.val .U32) value.dataCount value.codes Code.body value.data.length

/-- Data-count occurs before code despite its numerically larger section ID. -/
def DataCountSectionEncoding (value : Option U32)
    (bytes : List U8) : Prop :=
  PaddedEncoding (Source.readerByte WebAssembly.Binary.dataCountSectionId) StartEncoding none value bytes

/-- The Wasm 2.0 module format, parameterized by the code entry grammar, with custom
sections between the ordered optional sections. Typing checks are separate from this grammar. -/
def ModuleEncodingWith (codeRel : Code → List U8 → Prop) (value : Module) (bytes : List U8) : Prop :=
  WebAssembly.Binary.ModuleSectionsWith Source.readerByte CustomEncoding Leb128.Encoding
    (.vector Leb128.Encoding FuncTypeEncoding value.types) (.vector Leb128.Encoding ImportEncoding value.imports)
    (.vector Leb128.Encoding IndexEncoding value.functions) (.vector Leb128.Encoding TableTypeEncoding value.tables)
    (.vector Leb128.Encoding MemTypeEncoding value.memories) (.vector Leb128.Encoding GlobalEncoding value.globals)
    (.vector Leb128.Encoding ExportEncoding value.exports) (.index IndexEncoding value.start)
    (.vector Leb128.Encoding ElementEncoding value.elements) (.index IndexEncoding value.dataCount)
    (.vector Leb128.Encoding codeRel value.codes) (.vector Leb128.Encoding DataEncoding value.data)
    (DataCountValid value) bytes

/-- A section header at `start` with id `id` and a `u32` size. The payload runs from `first` to
`last` and lies entirely within `data`. -/
def SectionHeader (data : Slice U8) (start : Usize) (id : U8) (first last : Usize) : Prop :=
  ∃ pos size, At ByteEncoding data start id pos ∧ Binary.Leb128.Decoded data pos size first ∧
    last.val = first.val + size.val ∧ last.val ≤ data.length

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

end Itasca.Binary

end BinaryModuleGrammar
