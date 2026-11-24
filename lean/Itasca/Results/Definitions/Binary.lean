import Aeneas
import Itasca.Generated.FunsValidator
import Itasca.Generated.Types
import Itasca.Results.Definitions.Foundations
import «wasm2.0»

/-!
# Independent Wasm binary format

These definitions relate exact bytes to SpecTec syntax without running the validator. The
scalar and SIMD tables select source instructions directly; typing and implementation
limits are separate obligations. The independent grammar is necessary because the pinned
SpecTec-to-Lean translation does not yet translate the binary grammar. Nonminimal
permitted LEB encodings, exact floating-point bits, section order and declared-reference
conditions remain explicit.

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

/-- The binary type byte of a value type. -/
def valueByte : wasm_types.ValueType → U8
  | .I32 => 127#u8
  | .I64 => 126#u8
  | .F32 => 125#u8
  | .F64 => 124#u8
  | .V128 => 123#u8
  | .FuncRef => 112#u8
  | .ExternRef => 111#u8

end Itasca.Binary

/-!
## Numeric and empty block bytes

`ScalarBlockByte` gives the one-byte empty/numeric cases used within the complete
block-type grammar. It is an internal grammar decomposition, not a language mode.
-/

namespace Itasca.Body.Scalar
open Aeneas Aeneas.Std

/-- The one-byte spelling of an empty block type or a numeric result type. -/
inductive ScalarBlockByte : signature.BlockType → U8 → Prop where
  | empty : ScalarBlockByte .Empty 0x40#u8
  | i32 : ScalarBlockByte (.Value .I32) 0x7F#u8
  | i64 : ScalarBlockByte (.Value .I64) 0x7E#u8
  | f32 : ScalarBlockByte (.Value .F32) 0x7D#u8
  | f64 : ScalarBlockByte (.Value .F64) 0x7C#u8

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

/-- A flat instruction stream element: a plain instruction, a structured instruction header or
`else` or `end`. Block types may be type-section indices; the scalar-byte case
uses `ScalarBlockByte` internally. -/
inductive Token where
  | plain (op : instr)
  | block (bt : signature.BlockType)
  | loop (bt : signature.BlockType)
  | if_ (bt : signature.BlockType)
  | else_ | end_

/-- A plain token spells a well-formed instruction. The binary relation `Immediate` restricts
which plain tokens occur. -/
inductive Simple : Token → instr → Prop where
  | plain (op : instr) : wf_instr op → Simple (.plain op) op

/-- A flat token list spells a list of SpecTec instructions. An `if` with an empty else branch has
two spellings, with and without `else`. -/
inductive Emits : List Token → List instr → Prop where
  | nil : Emits [] []
  | simple {tokens ops token op} : Emits tokens ops → Simple token op →
      Emits (tokens ++ [token]) (ops ++ [op])
  | block {tokens ops bodyTokens body} (bt : signature.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.block bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.BLOCK (blockType bt) body])
  | loop {tokens ops bodyTokens body} (bt : signature.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.loop bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.LOOP (blockType bt) body])
  | ifElse {tokens ops thenTokens thenOps elseTokens elseOps} (bt : signature.BlockType) :
      Emits tokens ops → Emits thenTokens thenOps → Emits elseTokens elseOps →
      Emits (tokens ++ [.if_ bt] ++ thenTokens ++ [.else_] ++ elseTokens ++ [.end_])
        (ops ++ [.IFELSE (blockType bt) thenOps elseOps])
  | ifEnd {tokens ops bodyTokens body} (bt : signature.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.if_ bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.IFELSE (blockType bt) body []])

/-- A function body: tokens that spell the instructions, followed by the final `end`. -/
def BodyTokens (tokens : List Token) (ops : List instr) : Prop :=
  ∃ inner, tokens = inner ++ [.end_] ∧ Emits inner ops

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
def payload : List U8 → Nat
  | [] => 0
  | b :: bs => b.val % 128 + 128 * payload bs

/-- An unsigned 32-bit binary encoding, including permitted non-minimal encodings.
The first four bytes may carry seven bits each; a fifth carries only four. -/
def Encoding (bytes : List U8) (value : Nat) : Prop :=
  ∃ before last, bytes = before ++ [last] ∧ before.length ≤ 4 ∧
    (∀ b ∈ before, 128 ≤ b.val) ∧ last.val < 128 ∧
    (before.length = 4 → last.val < 16) ∧ value = payload bytes

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
  acc + (last.val : Int) * mult - if 64 ≤ last.val then 128 * mult else 0

variable (format : Format)

/-- Signed LEB128 bytes within the format's length and value bounds, permitting non-minimal sign
extension. -/
def Encoding (bytes : List U8) (value : Int) : Prop :=
  ∃ before last, bytes = before ++ [last] ∧ before.length ≤ format.last.val ∧
    (∀ b ∈ before, 128 ≤ b.val) ∧ last.val < 128 ∧
    value = finalValue (Binary.Leb128.payload before) (128 ^ before.length) last ∧
    format.lower.val ≤ value ∧ value ≤ format.upper.val

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
def payload : List U8 → Nat
  | [] => 0
  | b :: bs => b.val + 256 * payload bs

/-- Exactly `n` bytes whose little-endian value is the bit pattern. -/
def Encoding (n : Nat) (bytes : List U8) (bits : Nat) : Prop :=
  bytes.length = n ∧ bits = payload bytes

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
  .CONST .I32 (.mk_num__0 .I32 (.mk_uN (value.val % 4294967296).toNat))

end Itasca.Spec

namespace Itasca.Spec.Constants

/-- The SpecTec `i64.const` instruction for `value`, using its unsigned 64-bit bit pattern. -/
def i64 (value : I64) : instr :=
  .CONST .I64 (.mk_num__0 .I64 (.mk_uN (value.val % 18446744073709551616).toNat))

/-- The SpecTec float with the given IEEE field widths and bit pattern. Fields are translated
directly, so the sign of zero and NaN payloads are kept. -/
def floatValue (fractionBits exponentBits bits : Nat) : fN :=
  let fraction := bits % 2 ^ fractionBits
  let exponent := bits / 2 ^ fractionBits % 2 ^ exponentBits
  let magnitude :=
    if exponent = 0 then fNmag.SUBNORM fraction
    else if exponent = 2 ^ exponentBits - 1 then
      if fraction = 0 then fNmag.INF else fNmag.NAN fraction
    else fNmag.NORM fraction ((exponent : Int) - (2 ^ (exponentBits - 1) - 1 : Nat))
  if bits < 2 ^ (fractionBits + exponentBits) then .POS magnitude else .NEG magnitude

/-- The SpecTec `f32.const` instruction for the bit pattern `bits`. -/
def f32 (bits : U32) : instr := .CONST .F32 (.mk_num__1 .F32 (floatValue 23 8 bits.val))

/-- The SpecTec `f64.const` instruction for the bit pattern `bits`. -/
def f64 (bits : U64) : instr := .CONST .F64 (.mk_num__1 .F64 (floatValue 52 11 bits.val))

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

/-- The load or store opcode table, transcribed from the scalar specification. -/
def opcodeMeaning (opcode : U8) : Option Operation :=
  match opcode.val with
  | 0x28 => some (fullLoad .I32 .I32 2#u32)
  | 0x29 => some (fullLoad .I64 .I64 3#u32)
  | 0x2A => some (fullLoad .F32 .F32 2#u32)
  | 0x2B => some (fullLoad .F64 .F64 3#u32)
  | 0x2C => some (packedLoad .I32 .I32 8 .S 0#u32)
  | 0x2D => some (packedLoad .I32 .I32 8 .U 0#u32)
  | 0x2E => some (packedLoad .I32 .I32 16 .S 1#u32)
  | 0x2F => some (packedLoad .I32 .I32 16 .U 1#u32)
  | 0x30 => some (packedLoad .I64 .I64 8 .S 0#u32)
  | 0x31 => some (packedLoad .I64 .I64 8 .U 0#u32)
  | 0x32 => some (packedLoad .I64 .I64 16 .S 1#u32)
  | 0x33 => some (packedLoad .I64 .I64 16 .U 1#u32)
  | 0x34 => some (packedLoad .I64 .I64 32 .S 2#u32)
  | 0x35 => some (packedLoad .I64 .I64 32 .U 2#u32)
  | 0x36 => some (fullStore .I32 .I32 2#u32)
  | 0x37 => some (fullStore .I64 .I64 3#u32)
  | 0x38 => some (fullStore .F32 .F32 2#u32)
  | 0x39 => some (fullStore .F64 .F64 3#u32)
  | 0x3A => some (packedStore .I32 .I32 8 0#u32)
  | 0x3B => some (packedStore .I32 .I32 16 1#u32)
  | 0x3C => some (packedStore .I64 .I64 8 0#u32)
  | 0x3D => some (packedStore .I64 .I64 16 1#u32)
  | 0x3E => some (packedStore .I64 .I64 32 2#u32)
  | _ => none

end Itasca.Body.MemoryMeaning

namespace Itasca.Body.Numeric

/-- Scalar numeric bytes select a SpecTec instruction directly. Stack effects
and well-formedness are proved about this independent table in Binary; neither
is a premise of decoding. -/
def opcodeInstruction (opcode : U8) : Option instr :=
  match opcode.val with
  | 0x45 => some (.TESTOP .I32 (.mk_testop__0 .I32 .EQZ))
  | 0x46 => some (.RELOP .I32 (.mk_relop__0 .I32 (.EQ)))
  | 0x47 => some (.RELOP .I32 (.mk_relop__0 .I32 (.NE)))
  | 0x48 => some (.RELOP .I32 (.mk_relop__0 .I32 (.LT .S)))
  | 0x49 => some (.RELOP .I32 (.mk_relop__0 .I32 (.LT .U)))
  | 0x4A => some (.RELOP .I32 (.mk_relop__0 .I32 (.GT .S)))
  | 0x4B => some (.RELOP .I32 (.mk_relop__0 .I32 (.GT .U)))
  | 0x4C => some (.RELOP .I32 (.mk_relop__0 .I32 (.LE .S)))
  | 0x4D => some (.RELOP .I32 (.mk_relop__0 .I32 (.LE .U)))
  | 0x4E => some (.RELOP .I32 (.mk_relop__0 .I32 (.GE .S)))
  | 0x4F => some (.RELOP .I32 (.mk_relop__0 .I32 (.GE .U)))
  | 0x50 => some (.TESTOP .I64 (.mk_testop__0 .I64 .EQZ))
  | 0x51 => some (.RELOP .I64 (.mk_relop__0 .I64 (.EQ)))
  | 0x52 => some (.RELOP .I64 (.mk_relop__0 .I64 (.NE)))
  | 0x53 => some (.RELOP .I64 (.mk_relop__0 .I64 (.LT .S)))
  | 0x54 => some (.RELOP .I64 (.mk_relop__0 .I64 (.LT .U)))
  | 0x55 => some (.RELOP .I64 (.mk_relop__0 .I64 (.GT .S)))
  | 0x56 => some (.RELOP .I64 (.mk_relop__0 .I64 (.GT .U)))
  | 0x57 => some (.RELOP .I64 (.mk_relop__0 .I64 (.LE .S)))
  | 0x58 => some (.RELOP .I64 (.mk_relop__0 .I64 (.LE .U)))
  | 0x59 => some (.RELOP .I64 (.mk_relop__0 .I64 (.GE .S)))
  | 0x5A => some (.RELOP .I64 (.mk_relop__0 .I64 (.GE .U)))
  | 0x5B => some (.RELOP .F32 (.mk_relop__1 .F32 .EQ))
  | 0x5C => some (.RELOP .F32 (.mk_relop__1 .F32 .NE))
  | 0x5D => some (.RELOP .F32 (.mk_relop__1 .F32 .LT))
  | 0x5E => some (.RELOP .F32 (.mk_relop__1 .F32 .GT))
  | 0x5F => some (.RELOP .F32 (.mk_relop__1 .F32 .LE))
  | 0x60 => some (.RELOP .F32 (.mk_relop__1 .F32 .GE))
  | 0x61 => some (.RELOP .F64 (.mk_relop__1 .F64 .EQ))
  | 0x62 => some (.RELOP .F64 (.mk_relop__1 .F64 .NE))
  | 0x63 => some (.RELOP .F64 (.mk_relop__1 .F64 .LT))
  | 0x64 => some (.RELOP .F64 (.mk_relop__1 .F64 .GT))
  | 0x65 => some (.RELOP .F64 (.mk_relop__1 .F64 .LE))
  | 0x66 => some (.RELOP .F64 (.mk_relop__1 .F64 .GE))
  | 0x67 => some (.UNOP .I32 (.mk_unop__0 .I32 .CLZ))
  | 0x68 => some (.UNOP .I32 (.mk_unop__0 .I32 .CTZ))
  | 0x69 => some (.UNOP .I32 (.mk_unop__0 .I32 .POPCNT))
  | 0x6A => some (.BINOP .I32 (.mk_binop__0 .I32 (.ADD)))
  | 0x6B => some (.BINOP .I32 (.mk_binop__0 .I32 (.SUB)))
  | 0x6C => some (.BINOP .I32 (.mk_binop__0 .I32 (.MUL)))
  | 0x6D => some (.BINOP .I32 (.mk_binop__0 .I32 (.DIV .S)))
  | 0x6E => some (.BINOP .I32 (.mk_binop__0 .I32 (.DIV .U)))
  | 0x6F => some (.BINOP .I32 (.mk_binop__0 .I32 (.REM .S)))
  | 0x70 => some (.BINOP .I32 (.mk_binop__0 .I32 (.REM .U)))
  | 0x71 => some (.BINOP .I32 (.mk_binop__0 .I32 (.AND)))
  | 0x72 => some (.BINOP .I32 (.mk_binop__0 .I32 (.OR)))
  | 0x73 => some (.BINOP .I32 (.mk_binop__0 .I32 (.XOR)))
  | 0x74 => some (.BINOP .I32 (.mk_binop__0 .I32 (.SHL)))
  | 0x75 => some (.BINOP .I32 (.mk_binop__0 .I32 (.SHR .S)))
  | 0x76 => some (.BINOP .I32 (.mk_binop__0 .I32 (.SHR .U)))
  | 0x77 => some (.BINOP .I32 (.mk_binop__0 .I32 (.ROTL)))
  | 0x78 => some (.BINOP .I32 (.mk_binop__0 .I32 (.ROTR)))
  | 0x79 => some (.UNOP .I64 (.mk_unop__0 .I64 .CLZ))
  | 0x7A => some (.UNOP .I64 (.mk_unop__0 .I64 .CTZ))
  | 0x7B => some (.UNOP .I64 (.mk_unop__0 .I64 .POPCNT))
  | 0x7C => some (.BINOP .I64 (.mk_binop__0 .I64 (.ADD)))
  | 0x7D => some (.BINOP .I64 (.mk_binop__0 .I64 (.SUB)))
  | 0x7E => some (.BINOP .I64 (.mk_binop__0 .I64 (.MUL)))
  | 0x7F => some (.BINOP .I64 (.mk_binop__0 .I64 (.DIV .S)))
  | 0x80 => some (.BINOP .I64 (.mk_binop__0 .I64 (.DIV .U)))
  | 0x81 => some (.BINOP .I64 (.mk_binop__0 .I64 (.REM .S)))
  | 0x82 => some (.BINOP .I64 (.mk_binop__0 .I64 (.REM .U)))
  | 0x83 => some (.BINOP .I64 (.mk_binop__0 .I64 (.AND)))
  | 0x84 => some (.BINOP .I64 (.mk_binop__0 .I64 (.OR)))
  | 0x85 => some (.BINOP .I64 (.mk_binop__0 .I64 (.XOR)))
  | 0x86 => some (.BINOP .I64 (.mk_binop__0 .I64 (.SHL)))
  | 0x87 => some (.BINOP .I64 (.mk_binop__0 .I64 (.SHR .S)))
  | 0x88 => some (.BINOP .I64 (.mk_binop__0 .I64 (.SHR .U)))
  | 0x89 => some (.BINOP .I64 (.mk_binop__0 .I64 (.ROTL)))
  | 0x8A => some (.BINOP .I64 (.mk_binop__0 .I64 (.ROTR)))
  | 0x8B => some (.UNOP .F32 (.mk_unop__1 .F32 .ABS))
  | 0x8C => some (.UNOP .F32 (.mk_unop__1 .F32 .NEG))
  | 0x8D => some (.UNOP .F32 (.mk_unop__1 .F32 .CEIL))
  | 0x8E => some (.UNOP .F32 (.mk_unop__1 .F32 .FLOOR))
  | 0x8F => some (.UNOP .F32 (.mk_unop__1 .F32 .TRUNC))
  | 0x90 => some (.UNOP .F32 (.mk_unop__1 .F32 .NEAREST))
  | 0x91 => some (.UNOP .F32 (.mk_unop__1 .F32 .SQRT))
  | 0x92 => some (.BINOP .F32 (.mk_binop__1 .F32 .ADD))
  | 0x93 => some (.BINOP .F32 (.mk_binop__1 .F32 .SUB))
  | 0x94 => some (.BINOP .F32 (.mk_binop__1 .F32 .MUL))
  | 0x95 => some (.BINOP .F32 (.mk_binop__1 .F32 .DIV))
  | 0x96 => some (.BINOP .F32 (.mk_binop__1 .F32 .MIN))
  | 0x97 => some (.BINOP .F32 (.mk_binop__1 .F32 .MAX))
  | 0x98 => some (.BINOP .F32 (.mk_binop__1 .F32 .COPYSIGN))
  | 0x99 => some (.UNOP .F64 (.mk_unop__1 .F64 .ABS))
  | 0x9A => some (.UNOP .F64 (.mk_unop__1 .F64 .NEG))
  | 0x9B => some (.UNOP .F64 (.mk_unop__1 .F64 .CEIL))
  | 0x9C => some (.UNOP .F64 (.mk_unop__1 .F64 .FLOOR))
  | 0x9D => some (.UNOP .F64 (.mk_unop__1 .F64 .TRUNC))
  | 0x9E => some (.UNOP .F64 (.mk_unop__1 .F64 .NEAREST))
  | 0x9F => some (.UNOP .F64 (.mk_unop__1 .F64 .SQRT))
  | 0xA0 => some (.BINOP .F64 (.mk_binop__1 .F64 .ADD))
  | 0xA1 => some (.BINOP .F64 (.mk_binop__1 .F64 .SUB))
  | 0xA2 => some (.BINOP .F64 (.mk_binop__1 .F64 .MUL))
  | 0xA3 => some (.BINOP .F64 (.mk_binop__1 .F64 .DIV))
  | 0xA4 => some (.BINOP .F64 (.mk_binop__1 .F64 .MIN))
  | 0xA5 => some (.BINOP .F64 (.mk_binop__1 .F64 .MAX))
  | 0xA6 => some (.BINOP .F64 (.mk_binop__1 .F64 .COPYSIGN))
  | 0xA7 => some (.CVTOP .I32 .I64 (.mk_cvtop___0 .I64 .I32 (.WRAP)))
  | 0xA8 => some (.CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC .S)))
  | 0xA9 => some (.CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC .U)))
  | 0xAA => some (.CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC .S)))
  | 0xAB => some (.CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC .U)))
  | 0xAC => some (.CVTOP .I64 .I32 (.mk_cvtop___0 .I32 .I64 (.EXTEND .S)))
  | 0xAD => some (.CVTOP .I64 .I32 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U)))
  | 0xAE => some (.CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC .S)))
  | 0xAF => some (.CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC .U)))
  | 0xB0 => some (.CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC .S)))
  | 0xB1 => some (.CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC .U)))
  | 0xB2 => some (.CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 (.CONVERT .S)))
  | 0xB3 => some (.CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 (.CONVERT .U)))
  | 0xB4 => some (.CVTOP .F32 .I64 (.mk_cvtop___1 .I64 .F32 (.CONVERT .S)))
  | 0xB5 => some (.CVTOP .F32 .I64 (.mk_cvtop___1 .I64 .F32 (.CONVERT .U)))
  | 0xB6 => some (.CVTOP .F32 .F64 (.mk_cvtop___3 .F64 .F32 (.DEMOTE)))
  | 0xB7 => some (.CVTOP .F64 .I32 (.mk_cvtop___1 .I32 .F64 (.CONVERT .S)))
  | 0xB8 => some (.CVTOP .F64 .I32 (.mk_cvtop___1 .I32 .F64 (.CONVERT .U)))
  | 0xB9 => some (.CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 (.CONVERT .S)))
  | 0xBA => some (.CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 (.CONVERT .U)))
  | 0xBB => some (.CVTOP .F64 .F32 (.mk_cvtop___3 .F32 .F64 (.PROMOTE)))
  | 0xBC => some (.CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.REINTERPRET)))
  | 0xBD => some (.CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.REINTERPRET)))
  | 0xBE => some (.CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 (.REINTERPRET)))
  | 0xBF => some (.CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 (.REINTERPRET)))
  | _ => none

end Itasca.Body.Numeric

namespace Itasca.Body.Scalar

export Body (Token Simple Emits BodyTokens)

/-- `bytes` is the slice of `data` from `start` to `next`, followed by the untouched suffix. -/
structure BytesAt (data : Slice U8) (start : Usize) (bytes : List U8) (next : Usize) : Prop where
  suffix : data.val.drop start.val = bytes ++ data.val.drop next.val
  length : next.val = start.val + bytes.length
  bound : next.val ≤ data.length

/-- The concatenated unsigned LEB128 entries of an index vector, without the leading count. -/
inductive IndicesEncoding : List U32 → List U8 → Prop where
  | nil : IndicesEncoding [] []
  | cons {idx indices first rest} : Binary.Leb128.Encoding first idx.val →
      IndicesEncoding indices rest → IndicesEncoding (idx :: indices) (first ++ rest)

/-- The immediate bytes that follow an opcode byte for a scalar token. Literal opcode values,
the numeric and memory opcode tables and `ScalarBlockByte` define this reusable
internal grammar. `Body.Immediate` adds general block types, table indices and
the remaining instruction families for the complete body grammar. -/
inductive Immediate : U8 → Token → List U8 → Prop where
  | unreachable : Immediate 0x00#u8 (.plain .UNREACHABLE) []
  | nop : Immediate 0x01#u8 (.plain .NOP) []
  | block {bt b} : ScalarBlockByte bt b → Immediate 0x02#u8 (.block bt) [b]
  | loop {bt b} : ScalarBlockByte bt b → Immediate 0x03#u8 (.loop bt) [b]
  | if_ {bt b} : ScalarBlockByte bt b → Immediate 0x04#u8 (.if_ bt) [b]
  | else_ : Immediate 0x05#u8 .else_ []
  | end_ : Immediate 0x0B#u8 .end_ []
  | br (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x0C#u8 (.plain (.BR (.mk_uN idx.val))) bytes
  | brIf (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x0D#u8 (.plain (.BR_IF (.mk_uN idx.val))) bytes
  | brTable (indices : List U32) (default : U32) {count entries final} :
      Binary.Leb128.Encoding count indices.length → IndicesEncoding indices entries →
      Binary.Leb128.Encoding final default.val →
      Immediate 0x0E#u8 (.plain (.BR_TABLE (indices.map (fun i => .mk_uN i.val)) (.mk_uN default.val)))
        (count ++ entries ++ final)
  | return_ : Immediate 0x0F#u8 (.plain .RETURN) []
  | call (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x10#u8 (.plain (.CALL (.mk_uN idx.val))) bytes
  | callIndirect (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x11#u8 (.plain (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val))) (bytes ++ [0#u8])
  | drop : Immediate 0x1A#u8 (.plain .DROP) []
  | select : Immediate 0x1B#u8 (.plain (.SELECT none)) []
  | localGet (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x20#u8 (.plain (.LOCAL_GET (.mk_uN idx.val))) bytes
  | localSet (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x21#u8 (.plain (.LOCAL_SET (.mk_uN idx.val))) bytes
  | localTee (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x22#u8 (.plain (.LOCAL_TEE (.mk_uN idx.val))) bytes
  | globalGet (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x23#u8 (.plain (.GLOBAL_GET (.mk_uN idx.val))) bytes
  | globalSet (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      Immediate 0x24#u8 (.plain (.GLOBAL_SET (.mk_uN idx.val))) bytes
  | memory (opcode : U8) (operation : Body.MemoryMeaning.Operation) (arg : code.MemArg)
      {alignment offset} (meaning : Body.MemoryMeaning.opcodeMeaning opcode = some operation) :
      Binary.Leb128.Encoding alignment arg.align.val → Binary.Leb128.Encoding offset arg.offset.val →
      Immediate opcode (.plain (operation.op arg)) (alignment ++ offset)
  | memorySize : Immediate 0x3F#u8 (.plain .MEMORY_SIZE) [0#u8]
  | memoryGrow : Immediate 0x40#u8 (.plain .MEMORY_GROW) [0#u8]
  | i32Const (value : I32) {bytes} : Binary.SignedLeb32.Encoding bytes value.val →
      Immediate 0x41#u8 (.plain (Spec.i32Const value)) bytes
  | i64Const (value : I64) {bytes} : Binary.SignedLeb64.Encoding bytes value.val →
      Immediate 0x42#u8 (.plain (Spec.Constants.i64 value)) bytes
  | f32Const (bits : U32) {bytes} : Binary.FloatBits.Encoding 4 bytes bits.val →
      Immediate 0x43#u8 (.plain (Spec.Constants.f32 bits)) bytes
  | f64Const (bits : U64) {bytes} : Binary.FloatBits.Encoding 8 bytes bits.val →
      Immediate 0x44#u8 (.plain (Spec.Constants.f64 bits)) bytes
  | numericInstruction (opcode : U8) (source : instr)
      (meaning : Body.Numeric.opcodeInstruction opcode = some source) :
      Immediate opcode (.plain source) []

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
def declarations : _root_.module → List funcidx
  | .MODULE _ _ _ globals _ _ elements datas _ exports =>
    globals.flatMap globalIndices ++ elements.flatMap elementIndices ++
      datas.flatMap dataIndices ++ exports.flatMap exportIndices

/-- The declared-reference obligation on one function's complete instruction tree. -/
def Function (refs : List funcidx) : func → Prop
  | .FUNC _ _ body => Instructions refs body

/-- The reference-declaration condition missing from the generated specification. Occurrences
outside function bodies already belong to `declarations`, so only function bodies need a
membership check. The start index is neither a declaration nor a use of `ref.func`. -/
def Module (m : _root_.module) : Prop :=
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
inductive Immediate : U32 → instr → List U8 → Prop where
  | memoryInit (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 8#u32 (.MEMORY_INIT (.mk_uN index.val)) (bytes ++ [0#u8])
  | dataDrop (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 9#u32 (.DATA_DROP (.mk_uN index.val)) bytes
  | memoryCopy : Immediate 10#u32 .MEMORY_COPY [0#u8, 0#u8]
  | memoryFill : Immediate 11#u32 .MEMORY_FILL [0#u8]
  | tableInit (element table : U32) {elementBytes tableBytes} :
      Binary.Leb128.Encoding elementBytes element.val → Binary.Leb128.Encoding tableBytes table.val →
      Immediate 12#u32 (.TABLE_INIT (.mk_uN table.val) (.mk_uN element.val))
        (elementBytes ++ tableBytes)
  | elemDrop (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 13#u32 (.ELEM_DROP (.mk_uN index.val)) bytes
  | tableCopy (destination source : U32) {destinationBytes sourceBytes} :
      Binary.Leb128.Encoding destinationBytes destination.val → Binary.Leb128.Encoding sourceBytes source.val →
      Immediate 14#u32 (.TABLE_COPY (.mk_uN destination.val) (.mk_uN source.val))
        (destinationBytes ++ sourceBytes)
  | tableGrow (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 15#u32 (.TABLE_GROW (.mk_uN index.val)) bytes
  | tableSize (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 16#u32 (.TABLE_SIZE (.mk_uN index.val)) bytes
  | tableFill (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 17#u32 (.TABLE_FILL (.mk_uN index.val)) bytes

end Itasca.Body.BulkBinary

namespace Itasca.Body.NumericExtensions

/-- Independent sign opcode mapping into SpecTec syntax. -/
def signInstruction (opcode : U8) : Option instr :=
  match opcode.val with
  | 0xC0 => some (.UNOP .I32 (.mk_unop__0 .I32 (.EXTEND 8)))
  | 0xC1 => some (.UNOP .I32 (.mk_unop__0 .I32 (.EXTEND 16)))
  | 0xC2 => some (.UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 8)))
  | 0xC3 => some (.UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 16)))
  | 0xC4 => some (.UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 32)))
  | _ => none

/-- Independent saturating opcode mapping into SpecTec syntax. -/
def saturatingInstruction (opcode : U32) : Option instr :=
  match opcode.val with
  | 0 => some (.CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT .S)))
  | 1 => some (.CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT .U)))
  | 2 => some (.CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT .S)))
  | 3 => some (.CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT .U)))
  | 4 => some (.CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT .S)))
  | 5 => some (.CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT .U)))
  | 6 => some (.CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT .S)))
  | 7 => some (.CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT .U)))
  | _ => none

end Itasca.Body.NumericExtensions

namespace Itasca.Body.ReferencesBinary

/-- The reference type tag is the literal byte `0x70` or `0x6f`. -/
def referenceByte : wasm_types.ElemType → U8
  | .FuncRef => 0x70#u8
  | .ExternRef => 0x6f#u8

/-- The immediates of reference, typed select, table access and indirect call instructions. Index
encodings admit every valid unsigned LEB128. -/
inductive Immediate : U8 → instr → List U8 → Prop where
  | refNull (rt : wasm_types.ElemType) :
      Immediate 0xd0#u8 (.REF_NULL (Translation.referenceType rt)) [referenceByte rt]
  | refIsNull : Immediate 0xd1#u8 .REF_IS_NULL []
  | refFunc (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 0xd2#u8 (.REF_FUNC (.mk_uN index.val)) bytes
  | selectTyped (ty : wasm_types.ValueType) {count} : Binary.Leb128.Encoding count 1 →
      Immediate 0x1c#u8 (.SELECT (some [Translation.valueType ty])) (count ++ [Itasca.Binary.valueByte ty])
  | tableGet (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 0x25#u8 (.TABLE_GET (.mk_uN index.val)) bytes
  | tableSet (index : U32) {bytes} : Binary.Leb128.Encoding bytes index.val →
      Immediate 0x26#u8 (.TABLE_SET (.mk_uN index.val)) bytes
  | callIndirect (typeIndex tableIndex : U32) {typeBytes tableBytes} :
      Binary.Leb128.Encoding typeBytes typeIndex.val → Binary.Leb128.Encoding tableBytes tableIndex.val →
      Immediate 0x11#u8 (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val))
        (typeBytes ++ tableBytes)

end Itasca.Body.ReferencesBinary

namespace Itasca.Body.Simd

/-- The fourteen lane instructions, with the signedness forms Wasm 2.0 admits. -/
inductive LaneOperation where
  | i8x16ExtractS
  | i8x16ExtractU
  | i8x16Replace
  | i16x8ExtractS
  | i16x8ExtractU
  | i16x8Replace
  | i32x4Extract
  | i32x4Replace
  | i64x2Extract
  | i64x2Replace
  | f32x4Extract
  | f32x4Replace
  | f64x2Extract
  | f64x2Replace

/-- The vector shape of a lane instruction. -/
def LaneOperation.shape : LaneOperation → shape
  | .i8x16ExtractS => .X .I8 (.mk_dim 16)
  | .i8x16ExtractU => .X .I8 (.mk_dim 16)
  | .i8x16Replace => .X .I8 (.mk_dim 16)
  | .i16x8ExtractS => .X .I16 (.mk_dim 8)
  | .i16x8ExtractU => .X .I16 (.mk_dim 8)
  | .i16x8Replace => .X .I16 (.mk_dim 8)
  | .i32x4Extract => .X .I32 (.mk_dim 4)
  | .i32x4Replace => .X .I32 (.mk_dim 4)
  | .i64x2Extract => .X .I64 (.mk_dim 2)
  | .i64x2Replace => .X .I64 (.mk_dim 2)
  | .f32x4Extract => .X .F32 (.mk_dim 4)
  | .f32x4Replace => .X .F32 (.mk_dim 4)
  | .f64x2Extract => .X .F64 (.mk_dim 2)
  | .f64x2Replace => .X .F64 (.mk_dim 2)

/-- Whether the operation replaces a lane, as opposed to extracting one. -/
def LaneOperation.replace : LaneOperation → Bool
  | .i8x16ExtractS => false
  | .i8x16ExtractU => false
  | .i8x16Replace => true
  | .i16x8ExtractS => false
  | .i16x8ExtractU => false
  | .i16x8Replace => true
  | .i32x4Extract => false
  | .i32x4Replace => true
  | .i64x2Extract => false
  | .i64x2Replace => true
  | .f32x4Extract => false
  | .f32x4Replace => true
  | .f64x2Extract => false
  | .f64x2Replace => true

/-- The signedness of a packed extract, if any. -/
def LaneOperation.extension : LaneOperation → Option sx
  | .i8x16ExtractS => some .S
  | .i8x16ExtractU => some .U
  | .i8x16Replace => none
  | .i16x8ExtractS => some .S
  | .i16x8ExtractU => some .U
  | .i16x8Replace => none
  | .i32x4Extract => none
  | .i32x4Replace => none
  | .i64x2Extract => none
  | .i64x2Replace => none
  | .f32x4Extract => none
  | .f32x4Replace => none
  | .f64x2Extract => none
  | .f64x2Replace => none

/-- The SpecTec instruction of a lane operation at a lane index. -/
def LaneOperation.instruction (op : LaneOperation) (lane : laneidx) : instr :=
  if op.replace then .VREPLACE_LANE op.shape lane else .VEXTRACT_LANE op.shape op.extension lane

/-- The lane operation assigned to a `0xfd` subopcode (21 to 34). -/
def laneMeaning (opcode : Nat) : Option LaneOperation :=
  match opcode with
  | 21 => some .i8x16ExtractS
  | 22 => some .i8x16ExtractU
  | 23 => some .i8x16Replace
  | 24 => some .i16x8ExtractS
  | 25 => some .i16x8ExtractU
  | 26 => some .i16x8Replace
  | 27 => some .i32x4Extract
  | 28 => some .i32x4Replace
  | 29 => some .i64x2Extract
  | 30 => some .i64x2Replace
  | 31 => some .f32x4Extract
  | 32 => some .f32x4Replace
  | 33 => some .f64x2Extract
  | 34 => some .f64x2Replace
  | _ => none

/-- The vector memory instructions of Wasm 2.0. -/
inductive MemoryOperation where
  | load
  | load8x8S
  | load8x8U
  | load16x4S
  | load16x4U
  | load32x2S
  | load32x2U
  | splat8
  | splat16
  | splat32
  | splat64
  | storeFull
  | load8Lane
  | load16Lane
  | load32Lane
  | load64Lane
  | store8Lane
  | store16Lane
  | store32Lane
  | store64Lane
  | load32Zero
  | load64Zero

-- Elaboration-only parent preserves the shared generated memory-operation matcher.

/-- The lane count of a lane load or store, and 0 for the other operations. -/
def MemoryOperation.laneCount : MemoryOperation → Nat
  | .load => 0
  | .load8x8S => 0
  | .load8x8U => 0
  | .load16x4S => 0
  | .load16x4U => 0
  | .load32x2S => 0
  | .load32x2U => 0
  | .splat8 => 0
  | .splat16 => 0
  | .splat32 => 0
  | .splat64 => 0
  | .storeFull => 0
  | .load8Lane => 16
  | .load16Lane => 8
  | .load32Lane => 4
  | .load64Lane => 2
  | .store8Lane => 16
  | .store16Lane => 8
  | .store32Lane => 4
  | .store64Lane => 2
  | .load32Zero => 0
  | .load64Zero => 0

/-- The SpecTec instruction of a memory operation at a memory argument and lane index. The lane
index is ignored by operations without lanes. -/
def MemoryOperation.instruction (op : MemoryOperation) (arg : memarg) (lane : laneidx) : instr :=
  match op with
  | .load => .VLOAD .V128 none arg
  | .load8x8S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 8) 8 .S)) arg
  | .load8x8U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 8) 8 .U)) arg
  | .load16x4S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 16) 4 .S)) arg
  | .load16x4U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 16) 4 .U)) arg
  | .load32x2S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 32) 2 .S)) arg
  | .load32x2U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 32) 2 .U)) arg
  | .splat8 => .VLOAD .V128 (some (.SPLAT (.mk_sz 8))) arg
  | .splat16 => .VLOAD .V128 (some (.SPLAT (.mk_sz 16))) arg
  | .splat32 => .VLOAD .V128 (some (.SPLAT (.mk_sz 32))) arg
  | .splat64 => .VLOAD .V128 (some (.SPLAT (.mk_sz 64))) arg
  | .storeFull => .VSTORE .V128 arg
  | .load8Lane => .VLOAD_LANE .V128 (.mk_sz 8) arg lane
  | .load16Lane => .VLOAD_LANE .V128 (.mk_sz 16) arg lane
  | .load32Lane => .VLOAD_LANE .V128 (.mk_sz 32) arg lane
  | .load64Lane => .VLOAD_LANE .V128 (.mk_sz 64) arg lane
  | .store8Lane => .VSTORE_LANE .V128 (.mk_sz 8) arg lane
  | .store16Lane => .VSTORE_LANE .V128 (.mk_sz 16) arg lane
  | .store32Lane => .VSTORE_LANE .V128 (.mk_sz 32) arg lane
  | .store64Lane => .VSTORE_LANE .V128 (.mk_sz 64) arg lane
  | .load32Zero => .VLOAD .V128 (some (.ZERO (.mk_sz 32))) arg
  | .load64Zero => .VLOAD .V128 (some (.ZERO (.mk_sz 64))) arg

/-- The memory operation assigned to a `0xfd` subopcode. `load64_zero` is opcode 93 as in the
published specification. The pinned SpecTec binary table lists 92 twice. -/
def memoryMeaning (opcode : Nat) : Option MemoryOperation :=
  match opcode with
  | 0 => some .load
  | 1 => some .load8x8S
  | 2 => some .load8x8U
  | 3 => some .load16x4S
  | 4 => some .load16x4U
  | 5 => some .load32x2S
  | 6 => some .load32x2U
  | 7 => some .splat8
  | 8 => some .splat16
  | 9 => some .splat32
  | 10 => some .splat64
  | 11 => some .storeFull
  | 84 => some .load8Lane
  | 85 => some .load16Lane
  | 86 => some .load32Lane
  | 87 => some .load64Lane
  | 88 => some .store8Lane
  | 89 => some .store16Lane
  | 90 => some .store32Lane
  | 91 => some .store64Lane
  | 92 => some .load32Zero
  | 93 => some .load64Zero
  | _ => none

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

/-- Binary decoding into the specification AST, independent of typing. -/
def pureInstruction (subopcode : Nat) : Option instr :=
  if subopcode ≥ 256 then none else match subopcode with
  | 14 => some (.VSWIZZLE (.mk_ishape (.X .I8 (.mk_dim 16))))
  | 15 => some (.VSPLAT (.X .I8 (.mk_dim 16)))
  | 16 => some (.VSPLAT (.X .I16 (.mk_dim 8)))
  | 17 => some (.VSPLAT (.X .I32 (.mk_dim 4)))
  | 18 => some (.VSPLAT (.X .I64 (.mk_dim 2)))
  | 19 => some (.VSPLAT (.X .F32 (.mk_dim 4)))
  | 20 => some (.VSPLAT (.X .F64 (.mk_dim 2)))
  | 35 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 .EQ))
  | 36 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 .NE))
  | 37 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LT .S)))
  | 38 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LT .U)))
  | 39 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GT .S)))
  | 40 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GT .U)))
  | 41 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LE .S)))
  | 42 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LE .U)))
  | 43 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GE .S)))
  | 44 => some (.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GE .U)))
  | 45 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 .EQ))
  | 46 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 .NE))
  | 47 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LT .S)))
  | 48 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LT .U)))
  | 49 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GT .S)))
  | 50 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GT .U)))
  | 51 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LE .S)))
  | 52 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LE .U)))
  | 53 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GE .S)))
  | 54 => some (.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GE .U)))
  | 55 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 .EQ))
  | 56 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 .NE))
  | 57 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LT .S)))
  | 58 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LT .U)))
  | 59 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GT .S)))
  | 60 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GT .U)))
  | 61 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LE .S)))
  | 62 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LE .U)))
  | 63 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GE .S)))
  | 64 => some (.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GE .U)))
  | 65 => some (.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .EQ))
  | 66 => some (.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .NE))
  | 67 => some (.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .LT))
  | 68 => some (.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .GT))
  | 69 => some (.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .LE))
  | 70 => some (.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .GE))
  | 71 => some (.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .EQ))
  | 72 => some (.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .NE))
  | 73 => some (.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .LT))
  | 74 => some (.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .GT))
  | 75 => some (.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .LE))
  | 76 => some (.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .GE))
  | 77 => some (.VVUNOP .V128 .NOT)
  | 78 => some (.VVBINOP .V128 .AND)
  | 79 => some (.VVBINOP .V128 .ANDNOT)
  | 80 => some (.VVBINOP .V128 .OR)
  | 81 => some (.VVBINOP .V128 .XOR)
  | 82 => some (.VVTERNOP .V128 .BITSELECT)
  | 83 => some (.VVTESTOP .V128 .ANY_TRUE)
  | 94 => some (.VCVTOP (.X .F32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___3 .F64 2 .F32 4 (.DEMOTE .ZERO)))
  | 95 => some (.VCVTOP (.X .F64 (.mk_dim 2)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___3 .F32 4 .F64 2 .PROMOTELOW))
  | 96 => some (.VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .ABS))
  | 97 => some (.VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .NEG))
  | 98 => some (.VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .POPCNT))
  | 99 => some (.VTESTOP (.X .I8 (.mk_dim 16)) (.mk_vtestop__0 .I8 16 .ALL_TRUE))
  | 100 => some (.VBITMASK (.mk_ishape (.X .I8 (.mk_dim 16))))
  | 101 => some (.VNARROW (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_ishape (.X .I16 (.mk_dim 8))) .S)
  | 102 => some (.VNARROW (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_ishape (.X .I16 (.mk_dim 8))) .U)
  | 103 => some (.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .CEIL))
  | 104 => some (.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .FLOOR))
  | 105 => some (.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .TRUNC))
  | 106 => some (.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .NEAREST))
  | 107 => some (.VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 .SHL))
  | 108 => some (.VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 (.SHR .S)))
  | 109 => some (.VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 (.SHR .U)))
  | 110 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .ADD))
  | 111 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.ADD_SAT .S)))
  | 112 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.ADD_SAT .U)))
  | 113 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .SUB))
  | 114 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.SUB_SAT .S)))
  | 115 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.SUB_SAT .U)))
  | 116 => some (.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .CEIL))
  | 117 => some (.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .FLOOR))
  | 118 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MIN .S)))
  | 119 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MIN .U)))
  | 120 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MAX .S)))
  | 121 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MAX .U)))
  | 122 => some (.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .TRUNC))
  | 123 => some (.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .AVGRU))
  | 124 => some (.VEXTUNOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextunop___0 .I8 16 .I16 8 (.EXTADD_PAIRWISE .S)))
  | 125 => some (.VEXTUNOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextunop___0 .I8 16 .I16 8 (.EXTADD_PAIRWISE .U)))
  | 126 => some (.VEXTUNOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextunop___0 .I16 8 .I32 4 (.EXTADD_PAIRWISE .S)))
  | 127 => some (.VEXTUNOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextunop___0 .I16 8 .I32 4 (.EXTADD_PAIRWISE .U)))
  | 128 => some (.VUNOP (.X .I16 (.mk_dim 8)) (.mk_vunop__0 .I16 8 .ABS))
  | 129 => some (.VUNOP (.X .I16 (.mk_dim 8)) (.mk_vunop__0 .I16 8 .NEG))
  | 130 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .Q15MULR_SATS))
  | 131 => some (.VTESTOP (.X .I16 (.mk_dim 8)) (.mk_vtestop__0 .I16 8 .ALL_TRUE))
  | 132 => some (.VBITMASK (.mk_ishape (.X .I16 (.mk_dim 8))))
  | 133 => some (.VNARROW (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I32 (.mk_dim 4))) .S)
  | 134 => some (.VNARROW (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I32 (.mk_dim 4))) .U)
  | 135 => some (.VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .LOW .S)))
  | 136 => some (.VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .HIGH .S)))
  | 137 => some (.VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .LOW .U)))
  | 138 => some (.VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .HIGH .U)))
  | 139 => some (.VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 .SHL))
  | 140 => some (.VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 (.SHR .S)))
  | 141 => some (.VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 (.SHR .U)))
  | 142 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .ADD))
  | 143 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.ADD_SAT .S)))
  | 144 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.ADD_SAT .U)))
  | 145 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .SUB))
  | 146 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.SUB_SAT .S)))
  | 147 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.SUB_SAT .U)))
  | 148 => some (.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .NEAREST))
  | 149 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .MUL))
  | 150 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MIN .S)))
  | 151 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MIN .U)))
  | 152 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MAX .S)))
  | 153 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MAX .U)))
  | 155 => some (.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .AVGRU))
  | 156 => some (.VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .LOW .S)))
  | 157 => some (.VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .HIGH .S)))
  | 158 => some (.VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .LOW .U)))
  | 159 => some (.VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .HIGH .U)))
  | 160 => some (.VUNOP (.X .I32 (.mk_dim 4)) (.mk_vunop__0 .I32 4 .ABS))
  | 161 => some (.VUNOP (.X .I32 (.mk_dim 4)) (.mk_vunop__0 .I32 4 .NEG))
  | 163 => some (.VTESTOP (.X .I32 (.mk_dim 4)) (.mk_vtestop__0 .I32 4 .ALL_TRUE))
  | 164 => some (.VBITMASK (.mk_ishape (.X .I32 (.mk_dim 4))))
  | 167 => some (.VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .LOW .S)))
  | 168 => some (.VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .HIGH .S)))
  | 169 => some (.VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .LOW .U)))
  | 170 => some (.VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .HIGH .U)))
  | 171 => some (.VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 .SHL))
  | 172 => some (.VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 (.SHR .S)))
  | 173 => some (.VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 (.SHR .U)))
  | 174 => some (.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .ADD))
  | 177 => some (.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .SUB))
  | 181 => some (.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .MUL))
  | 182 => some (.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MIN .S)))
  | 183 => some (.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MIN .U)))
  | 184 => some (.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MAX .S)))
  | 185 => some (.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MAX .U)))
  | 186 => some (.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 .DOTS))
  | 188 => some (.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .LOW .S)))
  | 189 => some (.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .HIGH .S)))
  | 190 => some (.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .LOW .U)))
  | 191 => some (.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .HIGH .U)))
  | 192 => some (.VUNOP (.X .I64 (.mk_dim 2)) (.mk_vunop__0 .I64 2 .ABS))
  | 193 => some (.VUNOP (.X .I64 (.mk_dim 2)) (.mk_vunop__0 .I64 2 .NEG))
  | 195 => some (.VTESTOP (.X .I64 (.mk_dim 2)) (.mk_vtestop__0 .I64 2 .ALL_TRUE))
  | 196 => some (.VBITMASK (.mk_ishape (.X .I64 (.mk_dim 2))))
  | 199 => some (.VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .LOW .S)))
  | 200 => some (.VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .HIGH .S)))
  | 201 => some (.VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .LOW .U)))
  | 202 => some (.VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .HIGH .U)))
  | 203 => some (.VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 .SHL))
  | 204 => some (.VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 (.SHR .S)))
  | 205 => some (.VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 (.SHR .U)))
  | 206 => some (.VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .ADD))
  | 209 => some (.VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .SUB))
  | 213 => some (.VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .MUL))
  | 214 => some (.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 .EQ))
  | 215 => some (.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 .NE))
  | 216 => some (.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.LT .S)))
  | 217 => some (.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.GT .S)))
  | 218 => some (.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.LE .S)))
  | 219 => some (.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.GE .S)))
  | 220 => some (.VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .LOW .S)))
  | 221 => some (.VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .HIGH .S)))
  | 222 => some (.VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .LOW .U)))
  | 223 => some (.VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .HIGH .U)))
  | 224 => some (.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .ABS))
  | 225 => some (.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .NEG))
  | 227 => some (.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .SQRT))
  | 228 => some (.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .ADD))
  | 229 => some (.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .SUB))
  | 230 => some (.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MUL))
  | 231 => some (.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .DIV))
  | 232 => some (.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MIN))
  | 233 => some (.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MAX))
  | 234 => some (.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .PMIN))
  | 235 => some (.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .PMAX))
  | 236 => some (.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .ABS))
  | 237 => some (.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .NEG))
  | 239 => some (.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .SQRT))
  | 240 => some (.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .ADD))
  | 241 => some (.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .SUB))
  | 242 => some (.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MUL))
  | 243 => some (.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .DIV))
  | 244 => some (.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MIN))
  | 245 => some (.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MAX))
  | 246 => some (.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .PMIN))
  | 247 => some (.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .PMAX))
  | 248 => some (.VCVTOP (.X .I32 (.mk_dim 4)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___2 .F32 4 .I32 4 (.TRUNC_SAT .S none)))
  | 249 => some (.VCVTOP (.X .I32 (.mk_dim 4)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___2 .F32 4 .I32 4 (.TRUNC_SAT .U none)))
  | 250 => some (.VCVTOP (.X .F32 (.mk_dim 4)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F32 4 (.CONVERT none .S)))
  | 251 => some (.VCVTOP (.X .F32 (.mk_dim 4)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F32 4 (.CONVERT none .U)))
  | 252 => some (.VCVTOP (.X .I32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___2 .F64 2 .I32 4 (.TRUNC_SAT .S (some .ZERO))))
  | 253 => some (.VCVTOP (.X .I32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___2 .F64 2 .I32 4 (.TRUNC_SAT .U (some .ZERO))))
  | 254 => some (.VCVTOP (.X .F64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F64 2 (.CONVERT (some .LOW) .S)))
  | 255 => some (.VCVTOP (.X .F64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F64 2 (.CONVERT (some .LOW) .U)))
  | _ => none

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
def vectorConstant (low high : U64) : instr :=
  .VCONST .V128 (.mk_uN (low.val + high.val * 2 ^ 64))

/-- The first `count` little-endian bytes of a natural number. -/
def unpackBytes (bits : Nat) (count : Nat) : List Nat :=
  match count with
  | 0 => []
  | n + 1 => bits % 256 :: unpackBytes (bits / 256) n

/-- The sixteen lane indices of an `i8x16.shuffle`, from the bytes of its two 64-bit halves. -/
def shuffleIndices (low high : U64) : List laneidx :=
  ((unpackBytes low.val 8) ++ (unpackBytes high.val 8)).map uN.mk_uN

/-- An `i8x16.shuffle` with the lane indices of the two halves. -/
def shuffle (low high : U64) : instr :=
  .VSHUFFLE (.mk_ishape (.X .I8 (.mk_dim 16))) (shuffleIndices low high)

/-- The immediate bytes that follow a SIMD subopcode, including all valid `u32` LEB128 encodings of
memory arguments. The prefix and subopcode bytes belong to the enclosing grammar. -/
inductive Immediate : U32 → instr → List U8 → Prop where
  | pure (opcode : U32) (op : instr) : pureInstruction opcode.val = some op →
      Immediate opcode op []
  | lane (opcode : U32) (op : LaneOperation) (lane : U8) :
      laneMeaning opcode.val = some op →
      Immediate opcode (op.instruction (.mk_uN lane.val)) [lane]
  | memory (opcode : U32) (op : MemoryOperation) (arg : code.MemArg) {align offset} :
      memoryMeaning opcode.val = some op → op.laneCount = 0 →
      Binary.Leb128.Encoding align arg.align.val → Binary.Leb128.Encoding offset arg.offset.val →
      Immediate opcode (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN 0)) (align ++ offset)
  | memoryLane (opcode : U32) (op : MemoryOperation) (arg : code.MemArg) (lane : U8)
      {align offset} : memoryMeaning opcode.val = some op → op.laneCount ≠ 0 →
      Binary.Leb128.Encoding align arg.align.val → Binary.Leb128.Encoding offset arg.offset.val →
      Immediate opcode (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN lane.val))
        (align ++ offset ++ [lane])
  | constant (low high : U64) {lower upper} :
      Binary.FloatBits.Encoding 8 lower low.val → Binary.FloatBits.Encoding 8 upper high.val →
      Immediate 12#u32 (vectorConstant low high) (lower ++ upper)
  | shuffle (low high : U64) {lower upper} :
      Binary.FloatBits.Encoding 8 lower low.val → Binary.FloatBits.Encoding 8 upper high.val →
      Immediate 13#u32 (Simd.shuffle low high) (lower ++ upper)

end Itasca.Body.Simd

namespace Itasca.Body

/-- A block type as a literal tag byte or a nonnegative signed 33-bit type index. -/
def BlockEncoding (bt : signature.BlockType) (bytes : List U8) : Prop :=
  match bt with
  | .Empty => bytes = [64#u8]
  | .Value t => bytes = [Itasca.Binary.valueByte t]
  | .TypeIndex i => Binary.SignedLeb33.Encoding bytes i.val

/-- The immediate bytes that follow an opcode byte for a Wasm 2.0 token. Plain scalar leaves are
reused, but structured instructions take `BlockEncoding` block types. -/
inductive Immediate : U8 → Token → List U8 → Prop where
  | plain {opcode op bytes} : Body.Scalar.Immediate opcode (.plain op) bytes →
      Immediate opcode (.plain op) bytes
  | signExtensionInstruction (opcode : U8) (source : instr) :
      NumericExtensions.signInstruction opcode = some source →
      Immediate opcode (.plain source) []
  | saturatingInstruction (subopcode : U32) (source : instr) {bytes} :
      NumericExtensions.saturatingInstruction subopcode = some source →
      Binary.Leb128.Encoding bytes subopcode.val → Immediate 0xFC#u8 (.plain source) bytes
  | reference {opcode op bytes} : ReferencesBinary.Immediate opcode op bytes →
      Immediate opcode (.plain op) bytes
  | bulk (subopcode : U32) {prefixBytes op bytes} : Binary.Leb128.Encoding prefixBytes subopcode.val →
      BulkBinary.Immediate subopcode op bytes → Immediate 0xfc#u8 (.plain op) (prefixBytes ++ bytes)
  | simd (subopcode : U32) {prefixBytes op bytes} : Binary.Leb128.Encoding prefixBytes subopcode.val →
      Simd.Immediate subopcode op bytes → Immediate 0xfd#u8 (.plain op) (prefixBytes ++ bytes)
  | block {bt bytes} : BlockEncoding bt bytes → Immediate 0x02#u8 (.block bt) bytes
  | loop {bt bytes} : BlockEncoding bt bytes → Immediate 0x03#u8 (.loop bt) bytes
  | if_ {bt bytes} : BlockEncoding bt bytes → Immediate 0x04#u8 (.if_ bt) bytes
  | else_ : Immediate 0x05#u8 .else_ []
  | end_ : Immediate 0x0B#u8 .end_ []

/-- A token as its opcode byte followed by its immediate bytes. -/
def TokenEncoding (token : Token) (bytes : List U8) : Prop :=
  ∃ opcode immediate, bytes = opcode :: immediate ∧ Immediate opcode token immediate

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

/-- A list of values whose encodings, concatenated in order, form the byte list. -/
inductive Rep {α : Type} (R : α → List U8 → Prop) : List α → List U8 → Prop where
  | nil : Rep R [] []
  | cons {value values first rest} : R value first → Rep R values rest →
      Rep R (value :: values) (first ++ rest)

/-- A vector: a `u32` LEB128 count equal to the length, followed by the entries' encodings. -/
def VecEncoding {α : Type} (R : α → List U8 → Prop) (values : List α)
    (bytes : List U8) : Prop :=
  ∃ count entries, Binary.Leb128.Encoding count values.length ∧ Rep R values entries ∧
    bytes = count ++ entries

/-- An index as an unsigned LEB128 `u32`. -/
def IndexEncoding (index : U32) (bytes : List U8) : Prop :=
  Binary.Leb128.Encoding bytes index.val

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

/-- The binary type byte of a reference element type. -/
def elemByte : wasm_types.ElemType → U8
  | .FuncRef => 0x70#u8 | .ExternRef => 0x6F#u8

/-- A value type as its type byte. -/
def ValueTypeEncoding (ty : wasm_types.ValueType) (bytes : List U8) : Prop :=
  bytes = [Itasca.Binary.valueByte ty]

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
  bytes = [Itasca.Binary.valueByte ty.valtype, mutByte ty.mutability]

/-- A constant expression: one constant instruction followed by `end` (`0x0b`). -/
inductive ConstEncoding : wasm_types.ConstExpr → List U8 → Prop where
  | i32 (value : I32) {bytes} : Binary.SignedLeb32.Encoding bytes value.val →
      ConstEncoding (.I32 value) (0x41#u8 :: (bytes ++ [0x0B#u8]))
  | i64 (value : I64) {bytes} : Binary.SignedLeb64.Encoding bytes value.val →
      ConstEncoding (.I64 value) (0x42#u8 :: (bytes ++ [0x0B#u8]))
  | f32 (value : U32) {bytes} : Binary.FloatBits.Encoding 4 bytes value.val →
      ConstEncoding (.F32 value) (0x43#u8 :: (bytes ++ [0x0B#u8]))
  | f64 (value : U64) {bytes} : Binary.FloatBits.Encoding 8 bytes value.val →
      ConstEncoding (.F64 value) (0x44#u8 :: (bytes ++ [0x0B#u8]))
  | globalGet (index : U32) {bytes} : IndexEncoding index bytes →
      ConstEncoding (.GlobalGet index) (0x23#u8 :: (bytes ++ [0x0B#u8]))
  | refNull (ty : wasm_types.ElemType) :
      ConstEncoding (.RefNull ty) [0xD0#u8, elemByte ty, 0x0B#u8]
  | refFunc (index : U32) {bytes} : IndexEncoding index bytes →
      ConstEncoding (.RefFunc index) (0xD2#u8 :: (bytes ++ [0x0B#u8]))
  | v128 (low high : U64) {sub first rest} :
      IndexEncoding 12#u32 sub → Binary.FloatBits.Encoding 8 first low.val →
      Binary.FloatBits.Encoding 8 rest high.val →
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
inductive ElementEncoding : Element → List U8 → Prop where
  | activeIndices {offset initializers flags encodedOffset entries} :
      IndexEncoding 0#u32 flags → ConstEncoding offset encodedOffset →
      VecEncoding IndexEncoding initializers entries →
      ElementEncoding ⟨.FuncRef, .Active 0#u32 offset, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (flags ++ encodedOffset ++ entries)
  | passiveIndices {initializers flags entries} :
      IndexEncoding 1#u32 flags → VecEncoding IndexEncoding initializers entries →
      ElementEncoding ⟨.FuncRef, .Passive, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (flags ++ [0#u8] ++ entries)
  | explicitIndices {tableIndex offset initializers flags table encodedOffset entries} :
      IndexEncoding 2#u32 flags → IndexEncoding tableIndex table →
      ConstEncoding offset encodedOffset → VecEncoding IndexEncoding initializers entries →
      ElementEncoding ⟨.FuncRef, .Active tableIndex offset, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (flags ++ table ++ encodedOffset ++ [0#u8] ++ entries)
  | declarativeIndices {initializers flags entries} :
      IndexEncoding 3#u32 flags → VecEncoding IndexEncoding initializers entries →
      ElementEncoding ⟨.FuncRef, .Declarative, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (flags ++ [0#u8] ++ entries)
  | activeExpressions {offset initializers flags encodedOffset entries} :
      IndexEncoding 4#u32 flags → ConstEncoding offset encodedOffset →
      VecEncoding ConstEncoding initializers entries →
      ElementEncoding ⟨.FuncRef, .Active 0#u32 offset, initializers⟩
        (flags ++ encodedOffset ++ entries)
  | passiveExpressions {elem initializers flags entries} :
      IndexEncoding 5#u32 flags → VecEncoding ConstEncoding initializers entries →
      ElementEncoding ⟨elem, .Passive, initializers⟩
        (flags ++ [elemByte elem] ++ entries)
  | explicitExpressions {elem tableIndex offset initializers flags table encodedOffset entries} :
      IndexEncoding 6#u32 flags → IndexEncoding tableIndex table →
      ConstEncoding offset encodedOffset → VecEncoding ConstEncoding initializers entries →
      ElementEncoding ⟨elem, .Active tableIndex offset, initializers⟩
        (flags ++ table ++ encodedOffset ++ [elemByte elem] ++ entries)
  | declarativeExpressions {elem initializers flags entries} :
      IndexEncoding 7#u32 flags → VecEncoding ConstEncoding initializers entries →
      ElementEncoding ⟨elem, .Declarative, initializers⟩
        (flags ++ [elemByte elem] ++ entries)

/-- The active segment flag forms of a data segment, including non-minimal unsigned LEBs. -/
inductive ActiveIndexEncoding : U32 → Bool → List U8 → Prop where
  | implicit {flags} : IndexEncoding 0#u32 flags → ActiveIndexEncoding 0#u32 false flags
  | explicit {index flags bytes} : IndexEncoding 2#u32 flags → IndexEncoding index bytes →
      ActiveIndexEncoding index true (flags ++ bytes)

/-- A local declaration: a count followed by a value type byte. -/
def LocalEncoding (entry : U32 × wasm_types.ValueType) (bytes : List U8) : Prop :=
  ∃ count, IndexEncoding entry.1 count ∧ bytes = count ++ [Itasca.Binary.valueByte entry.2]

/-- The Wasm 2.0 data segment encodings: active (flag `0` or `2`) and passive (flag `1`). -/
inductive DataEncoding : Data → List U8 → Prop where
  | active {memoryIndex offset init explicit index encodedOffset entries} :
      ActiveIndexEncoding memoryIndex explicit index → ConstEncoding offset encodedOffset →
      ByteVecEncoding init entries →
      DataEncoding ⟨.Active memoryIndex offset, init⟩ (index ++ encodedOffset ++ entries)
  | passive {init flags entries} :
      IndexEncoding 1#u32 flags → ByteVecEncoding init entries →
      DataEncoding ⟨.Passive, init⟩ (flags ++ entries)

/-- A section: its id, a LEB128 size equal to the payload length, and the payload. -/
def SectionEncoding {α : Type} (id : U8) (R : α → List U8 → Prop)
    (value : α) (bytes : List U8) : Prop :=
  ∃ size payload, Binary.Leb128.Encoding size payload.length ∧ R value payload ∧
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

/-- The start section payload: a function index. -/
def StartEncoding (value : Option U32) (bytes : List U8) : Prop :=
  ∃ index, value = some index ∧ IndexEncoding index bytes

/-- The module header: magic bytes `\0asm` and binary format version 1.
Wasm 2.0 uses this same binary version; it does not select a runtime profile. -/
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
    PaddedEncoding 9#u8 (VecEncoding ElementEncoding) [] value.elements elements ∧
    DataCountSectionEncoding value.dataCount dataCount ∧
    PaddedEncoding 10#u8 (VecEncoding codeRel) [] value.codes codes ∧
    PaddedEncoding 11#u8 (VecEncoding DataEncoding) [] value.data datas ∧
    CustomsEncoding customs ∧
    bytes = magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
      globals ++ exports ++ start ++ elements ++ dataCount ++ codes ++ datas ++ customs ∧
    DataCountValid value

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
