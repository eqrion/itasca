import WebAssembly

namespace WebAssembly.Binary

namespace Numeric

/-- Scalar numeric bytes select a SpecTec instruction directly. Stack effects
and well-formedness are proved about this independent table in Binary; neither
is a premise of decoding. -/
def opcodeInstruction (opcode : UInt8) : Option instr :=
  match opcode.toNat with
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

end Numeric

namespace NumericExtensions
/-- Independent sign opcode mapping into SpecTec syntax. -/
def signInstruction (opcode : UInt8) : Option instr :=
  match opcode.toNat with
  | 0xC0 => some (.UNOP .I32 (.mk_unop__0 .I32 (.EXTEND 8)))
  | 0xC1 => some (.UNOP .I32 (.mk_unop__0 .I32 (.EXTEND 16)))
  | 0xC2 => some (.UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 8)))
  | 0xC3 => some (.UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 16)))
  | 0xC4 => some (.UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 32)))
  | _ => none

/-- Independent saturating opcode mapping into SpecTec syntax. -/
def saturatingInstruction (opcode : Nat) : Option instr :=
  match opcode with
  | 0 => some (.CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT .S)))
  | 1 => some (.CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT .U)))
  | 2 => some (.CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT .S)))
  | 3 => some (.CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT .U)))
  | 4 => some (.CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT .S)))
  | 5 => some (.CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT .U)))
  | 6 => some (.CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT .S)))
  | 7 => some (.CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT .U)))
  | _ => none

end NumericExtensions

namespace Simd
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

end Simd

end WebAssembly.Binary
