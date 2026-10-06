import Itasca.TypeTranslation

open Aeneas Aeneas.Std

namespace Itasca.MemoryMeaning

def memArg (arg : code.MemArg) : memarg :=
  { ALIGN := .mk_uN arg.align.val, OFFSET := .mk_uN arg.offset.val }

/-- An independent Wasm 1.0 memory opcode row. -/
structure Operation where
  ty : types.ValueType
  naturalAlign : U32
  store : Bool
  op : code.MemArg → instr

def fullLoad (ty : types.ValueType) (nt : numtype) (alignment : U32) : Operation :=
  ⟨ty, alignment, false, fun arg => .LOAD nt none (memArg arg)⟩

def packedLoad (ty : types.ValueType) (it : Inn) (width : Nat)
    (extension : sx) (alignment : U32) : Operation :=
  ⟨ty, alignment, false, fun arg =>
    .LOAD (numtype_Inn it) (some (.mk_loadop__0 it (.mk_loadop_Inn (.mk_sz width) extension))) (memArg arg)⟩

def fullStore (ty : types.ValueType) (nt : numtype) (alignment : U32) : Operation :=
  ⟨ty, alignment, true, fun arg => .STORE nt none (memArg arg)⟩

def packedStore (ty : types.ValueType) (it : Inn) (width : Nat) (alignment : U32) : Operation :=
  ⟨ty, alignment, true, fun arg => .STORE (numtype_Inn it) (some (.mk_sz width)) (memArg arg)⟩

/-- Literal opcode-to-instruction transcription, separate from extracted dispatch tables. -/
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

end Itasca.MemoryMeaning
