import WebAssembly.Binary.Types

namespace WebAssembly.Binary

namespace MemoryMeaning

/-- A row of the memory opcode table: the value type, the natural alignment exponent, whether it is
a store, and the instruction built from a memory argument. -/
structure Operation where
  ty : ValueType
  naturalAlign : Nat
  store : Bool
  op : memarg → instr

/-- A load of the full width of a number type. -/
def fullLoad (ty : ValueType) (nt : numtype) (alignment : Nat) : Operation :=
  ⟨ty, alignment, false, fun arg => .LOAD nt none arg⟩

/-- A packed integer load of the given bit width and signedness. -/
def packedLoad (ty : ValueType) (it : Inn) (width : Nat)
    (extension : sx) (alignment : Nat) : Operation :=
  ⟨ty, alignment, false, fun arg =>
    .LOAD (numtype_Inn it) (some (.mk_loadop__0 it (.mk_loadop_Inn (.mk_sz width) extension))) arg⟩

/-- A store of the full width of a number type. -/
def fullStore (ty : ValueType) (nt : numtype) (alignment : Nat) : Operation :=
  ⟨ty, alignment, true, fun arg => .STORE nt none arg⟩

/-- A packed integer store of the given bit width. -/
def packedStore (ty : ValueType) (it : Inn) (width : Nat) (alignment : Nat) : Operation :=
  ⟨ty, alignment, true, fun arg => .STORE (numtype_Inn it) (some (.mk_sz width)) arg⟩

/-- The load or store opcode table, transcribed from the scalar specification. -/
def opcodeTable (opcode : Nat)
    (fullLoad : ValueType → numtype → Nat → α)
    (packedLoad : ValueType → Inn → Nat → sx → Nat → α)
    (fullStore : ValueType → numtype → Nat → α)
    (packedStore : ValueType → Inn → Nat → Nat → α) : Option α :=
  match opcode with
  | 0x28 => some (fullLoad .I32 .I32 2)
  | 0x29 => some (fullLoad .I64 .I64 3)
  | 0x2A => some (fullLoad .F32 .F32 2)
  | 0x2B => some (fullLoad .F64 .F64 3)
  | 0x2C => some (packedLoad .I32 .I32 8 .S 0)
  | 0x2D => some (packedLoad .I32 .I32 8 .U 0)
  | 0x2E => some (packedLoad .I32 .I32 16 .S 1)
  | 0x2F => some (packedLoad .I32 .I32 16 .U 1)
  | 0x30 => some (packedLoad .I64 .I64 8 .S 0)
  | 0x31 => some (packedLoad .I64 .I64 8 .U 0)
  | 0x32 => some (packedLoad .I64 .I64 16 .S 1)
  | 0x33 => some (packedLoad .I64 .I64 16 .U 1)
  | 0x34 => some (packedLoad .I64 .I64 32 .S 2)
  | 0x35 => some (packedLoad .I64 .I64 32 .U 2)
  | 0x36 => some (fullStore .I32 .I32 2)
  | 0x37 => some (fullStore .I64 .I64 3)
  | 0x38 => some (fullStore .F32 .F32 2)
  | 0x39 => some (fullStore .F64 .F64 3)
  | 0x3A => some (packedStore .I32 .I32 8 0)
  | 0x3B => some (packedStore .I32 .I32 16 1)
  | 0x3C => some (packedStore .I64 .I64 8 0)
  | 0x3D => some (packedStore .I64 .I64 16 1)
  | 0x3E => some (packedStore .I64 .I64 32 2)
  | _ => none

def opcodeMeaning (opcode : UInt8) : Option Operation :=
  opcodeTable opcode.toNat fullLoad packedLoad fullStore packedStore

end MemoryMeaning

end WebAssembly.Binary
