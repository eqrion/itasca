import WebAssembly
import WebAssembly.Binary.Leb128

namespace WebAssembly.Binary

/-- Value types with a binary spelling. The abstract typing language also has BOT. -/
inductive ValueType where
  | I32 | I64 | F32 | F64 | V128 | FUNCREF | EXTERNREF
  deriving DecidableEq

def ValueType.toSpec : ValueType → valtype
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64
  | .V128 => .V128
  | .FUNCREF => .FUNCREF
  | .EXTERNREF => .EXTERNREF

/-- The binary type byte of a value type. -/
def valueByte : ValueType → UInt8
  | .I32 => 127
  | .I64 => 126
  | .F32 => 125
  | .F64 => 124
  | .V128 => 123
  | .FUNCREF => 112
  | .EXTERNREF => 111

namespace FloatBits

def payloadWith (byte : β → Nat) : List β → Nat
  | [] => 0
  | b :: bs => byte b + 256 * payloadWith byte bs

abbrev payload := payloadWith UInt8.toNat

def EncodingForm (payload : List β → Nat) (n : Nat) (bytes : List β) (bits : Nat) : Prop :=
  bytes.length = n ∧ bits = payload bytes

abbrev Encoding := EncodingForm payload

end FloatBits

namespace Constants
/-- The SpecTec `i32.const` instruction for `value`, using its unsigned 32-bit bit pattern. -/
def i32Const (value : Int) : instr :=
  .CONST .I32 (.mk_num__0 .I32 (.mk_uN (value % 4294967296).toNat))

/-- The SpecTec `i64.const` instruction for `value`, using its unsigned 64-bit bit pattern. -/
def i64 (value : Int) : instr :=
  .CONST .I64 (.mk_num__0 .I64 (.mk_uN (value % 18446744073709551616).toNat))

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
def f32 (bits : Nat) : instr := .CONST .F32 (.mk_num__1 .F32 (floatValue 23 8 bits))

/-- The SpecTec `f64.const` instruction for the bit pattern `bits`. -/
def f64 (bits : Nat) : instr := .CONST .F64 (.mk_num__1 .F64 (floatValue 52 11 bits))

end Constants

end WebAssembly.Binary
