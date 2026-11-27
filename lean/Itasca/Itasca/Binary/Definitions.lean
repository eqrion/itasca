import Itasca.Results.Definitions.Binary

open WebAssembly

/-! Proof helpers for intermediate states; public results use the semantic
vocabulary in Interface. Keeping these here avoids exposing parser progress
and implementation accounting as part of the public contract. -/

namespace Itasca.Spec.DeclaredReferences
open Aeneas Aeneas.Std Itasca

/-- All `ref.func` occurrences in one instruction have declarations in `refs`. -/
def Instruction (refs : List funcidx) (op : instr) : Prop :=
  ∀ x ∈ instructionIndices false op, x ∈ refs

end Itasca.Spec.DeclaredReferences

namespace Itasca.Body.Simd
open Aeneas Aeneas.Std Itasca

/-- The scalar type moved in or out of a lane. -/
def LaneOperation.scalar : LaneOperation → numtype
  | .i8x16ExtractS => .I32
  | .i8x16ExtractU => .I32
  | .i8x16Replace => .I32
  | .i16x8ExtractS => .I32
  | .i16x8ExtractU => .I32
  | .i16x8Replace => .I32
  | .i32x4Extract => .I32
  | .i32x4Replace => .I32
  | .i64x2Extract => .I64
  | .i64x2Replace => .I64
  | .f32x4Extract => .F32
  | .f32x4Replace => .F32
  | .f64x2Extract => .F64
  | .f64x2Replace => .F64

end Itasca.Body.Simd

namespace Itasca.Body.Simd
open Aeneas Aeneas.Std Itasca

/-- The operand types of a lane operation. -/
def LaneOperation.inputs (op : LaneOperation) : List valtype :=
  if op.replace then [.V128, valtype_numtype op.scalar] else [.V128]

end Itasca.Body.Simd

namespace Itasca.Body.Simd
open Aeneas Aeneas.Std Itasca

/-- The result types of a lane operation. -/
def LaneOperation.outputs (op : LaneOperation) : List valtype :=
  if op.replace then [.V128] else [valtype_numtype op.scalar]

end Itasca.Body.Simd

namespace Itasca.Body.Simd
open Aeneas Aeneas.Std Itasca

/-- The natural alignment exponent of a memory operation. -/
def MemoryOperation.naturalAlign : MemoryOperation → Nat
  | .load => 4
  | .load8x8S => 3
  | .load8x8U => 3
  | .load16x4S => 3
  | .load16x4U => 3
  | .load32x2S => 3
  | .load32x2U => 3
  | .splat8 => 0
  | .splat16 => 1
  | .splat32 => 2
  | .splat64 => 3
  | .storeFull => 4
  | .load8Lane => 0
  | .load16Lane => 1
  | .load32Lane => 2
  | .load64Lane => 3
  | .store8Lane => 0
  | .store16Lane => 1
  | .store32Lane => 2
  | .store64Lane => 3
  | .load32Zero => 2
  | .load64Zero => 3

end Itasca.Body.Simd

namespace Itasca.Body.Simd
open Aeneas Aeneas.Std Itasca

/-- Whether the operation writes memory. -/
def MemoryOperation.store : MemoryOperation → Bool
  | .load => false
  | .load8x8S => false
  | .load8x8U => false
  | .load16x4S => false
  | .load16x4U => false
  | .load32x2S => false
  | .load32x2U => false
  | .splat8 => false
  | .splat16 => false
  | .splat32 => false
  | .splat64 => false
  | .storeFull => true
  | .load8Lane => false
  | .load16Lane => false
  | .load32Lane => false
  | .load64Lane => false
  | .store8Lane => true
  | .store16Lane => true
  | .store32Lane => true
  | .store64Lane => true
  | .load32Zero => false
  | .load64Zero => false

end Itasca.Body.Simd

namespace Itasca.Body.Simd
open Aeneas Aeneas.Std Itasca

/-- The operand types of a memory operation. -/
def MemoryOperation.inputs (op : MemoryOperation) : List valtype :=
  if op.store || op.laneCount != 0 then [.I32, .V128] else [.I32]

end Itasca.Body.Simd

namespace Itasca.Body.Simd
open Aeneas Aeneas.Std Itasca

/-- The result types of a memory operation. -/
def MemoryOperation.outputs (op : MemoryOperation) : List valtype :=
  if op.store then [] else [.V128]

end Itasca.Body.Simd

namespace Itasca.Body
open Aeneas Aeneas.Std Itasca

/-- Only plain instruction tokens carry declared-reference obligations. -/
def Token.Declared (refs : List funcidx) : Token → Prop
  | .plain op => Spec.DeclaredReferences.Instruction refs op
  | _ => True

end Itasca.Body

namespace Itasca.Body
open Aeneas Aeneas.Std Itasca

/-- Every token of the list meets its declared-reference obligation. -/
def TokensDeclared (refs : List funcidx) (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, token.Declared refs

end Itasca.Body
