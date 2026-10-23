import Exec.Abs.Memory.Descriptor
import Exec.Generated.Equations
namespace Exec.Code
open Aeneas Aeneas.Std

def memoryLoadOpcode : Abs.Memory.Load → U16
  | .full .I32 => 40#u16
  | .full .I64 => 41#u16
  | .full .F32 => 42#u16
  | .full .F64 => 43#u16
  | .packed .I32 .byte .S => 44#u16
  | .packed .I32 .byte .U => 45#u16
  | .packed .I32 .half .S => 46#u16
  | .packed .I32 .half .U => 47#u16
  | .packed .I64 .byte .S => 48#u16
  | .packed .I64 .byte .U => 49#u16
  | .packed .I64 .half .S => 50#u16
  | .packed .I64 .half .U => 51#u16
  | .packed .I64 .word .S => 52#u16
  | .packed .I64 .word .U => 53#u16

def memoryStoreOpcode : Abs.Memory.Store → U16
  | .full .I32 => 54#u16
  | .full .I64 => 55#u16
  | .full .F32 => 56#u16
  | .full .F64 => 57#u16
  | .packed .I32 .byte => 58#u16
  | .packed .I32 .half => 59#u16
  | .packed .I64 .byte => 60#u16
  | .packed .I64 .half => 61#u16
  | .packed .I64 .word => 62#u16

def memoryLoadInstruction (op : Abs.Memory.Load) (dst address offset : U32) : runtime.bytecode.Instr :=
  match op with
  | .full .I32 => .I32Load dst address offset
  | .full .I64 => .I64Load dst address offset
  | .full .F32 => .F32Load dst address offset
  | .full .F64 => .F64Load dst address offset
  | .packed .I32 .byte .S => .I32Load8S dst address offset
  | .packed .I32 .byte .U => .I32Load8U dst address offset
  | .packed .I32 .half .S => .I32Load16S dst address offset
  | .packed .I32 .half .U => .I32Load16U dst address offset
  | .packed .I64 .byte .S => .I64Load8S dst address offset
  | .packed .I64 .byte .U => .I64Load8U dst address offset
  | .packed .I64 .half .S => .I64Load16S dst address offset
  | .packed .I64 .half .U => .I64Load16U dst address offset
  | .packed .I64 .word .S => .I64Load32S dst address offset
  | .packed .I64 .word .U => .I64Load32U dst address offset

def memoryStoreInstruction (op : Abs.Memory.Store) (address value offset : U32) : runtime.bytecode.Instr :=
  match op with
  | .full .I32 => .I32Store address value offset
  | .full .I64 => .I64Store address value offset
  | .full .F32 => .F32Store address value offset
  | .full .F64 => .F64Store address value offset
  | .packed .I32 .byte => .I32Store8 address value offset
  | .packed .I32 .half => .I32Store16 address value offset
  | .packed .I64 .byte => .I64Store8 address value offset
  | .packed .I64 .half => .I64Store16 address value offset
  | .packed .I64 .word => .I64Store32 address value offset

theorem memoryLoadInstruction_make (op : Abs.Memory.Load) (dst address offset : U32) :
    runtime.bytecode.Instr.make_load (memoryLoadOpcode op) dst address offset =
      .ok (some (memoryLoadInstruction op dst address offset)) := by
  cases op with
  | full ty => cases ty <;> rfl
  | packed ty width sign => cases ty <;> cases width <;> cases sign <;> rfl

theorem memoryStoreInstruction_make (op : Abs.Memory.Store) (address value offset : U32) :
    runtime.bytecode.Instr.make_store (memoryStoreOpcode op) address value offset =
      .ok (some (memoryStoreInstruction op address value offset)) := by
  cases op with
  | full ty => cases ty <;> rfl
  | packed ty width => cases ty <;> cases width <;> rfl
end Exec.Code
