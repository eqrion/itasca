import Exec.Abs.State

namespace Exec.Abs.Stateful

/-- Source-indexed reference, table and bulk-memory instructions. -/
inductive Instruction where
  | refNull (type : reftype)
  | refFunc (function : Nat)
  | refIsNull
  | tableGet (table : Nat)
  | tableSet (table : Nat)
  | tableSize (table : Nat)
  | tableGrow (table : Nat)
  | tableFill (table : Nat)
  | tableCopy (destination source : Nat)
  | tableInit (table element : Nat)
  | elemDrop (element : Nat)
  | memorySize
  | memoryGrow
  | memoryFill
  | memoryCopy
  | memoryInit (data : Nat)
  | dataDrop (data : Nat)

def Instruction.source : Instruction → instr
  | .refNull type => .REF_NULL type
  | .refFunc function => .REF_FUNC (.mk_uN function)
  | .refIsNull => .REF_IS_NULL
  | .tableGet table => .TABLE_GET (.mk_uN table)
  | .tableSet table => .TABLE_SET (.mk_uN table)
  | .tableSize table => .TABLE_SIZE (.mk_uN table)
  | .tableGrow table => .TABLE_GROW (.mk_uN table)
  | .tableFill table => .TABLE_FILL (.mk_uN table)
  | .tableCopy destination source => .TABLE_COPY (.mk_uN destination) (.mk_uN source)
  | .tableInit table element => .TABLE_INIT (.mk_uN table) (.mk_uN element)
  | .elemDrop element => .ELEM_DROP (.mk_uN element)
  | .memorySize => .MEMORY_SIZE
  | .memoryGrow => .MEMORY_GROW
  | .memoryFill => .MEMORY_FILL
  | .memoryCopy => .MEMORY_COPY
  | .memoryInit data => .MEMORY_INIT (.mk_uN data)
  | .dataDrop data => .DATA_DROP (.mk_uN data)

def decodeInstruction : instr → Option Instruction
  | .REF_NULL type => some (.refNull type)
  | .REF_FUNC (.mk_uN function) => some (.refFunc function)
  | .REF_IS_NULL => some .refIsNull
  | .TABLE_GET (.mk_uN table) => some (.tableGet table)
  | .TABLE_SET (.mk_uN table) => some (.tableSet table)
  | .TABLE_SIZE (.mk_uN table) => some (.tableSize table)
  | .TABLE_GROW (.mk_uN table) => some (.tableGrow table)
  | .TABLE_FILL (.mk_uN table) => some (.tableFill table)
  | .TABLE_COPY (.mk_uN destination) (.mk_uN source) => some (.tableCopy destination source)
  | .TABLE_INIT (.mk_uN table) (.mk_uN element) => some (.tableInit table element)
  | .ELEM_DROP (.mk_uN element) => some (.elemDrop element)
  | .MEMORY_SIZE => some .memorySize
  | .MEMORY_GROW => some .memoryGrow
  | .MEMORY_FILL => some .memoryFill
  | .MEMORY_COPY => some .memoryCopy
  | .MEMORY_INIT (.mk_uN data) => some (.memoryInit data)
  | .DATA_DROP (.mk_uN data) => some (.dataDrop data)
  | _ => none

@[simp] theorem decode_source (op : Instruction) : decodeInstruction op.source = some op := by
  cases op <;> rfl

theorem source_injective {left right : Instruction} (same : left.source = right.source) :
    left = right := by
  have h := congrArg decodeInstruction same
  simpa only [decode_source, Option.some.injEq] using h

/-- Operand counts do not depend on the table element type. -/
def Instruction.arity : Instruction → Nat
  | .refNull _ | .refFunc _ | .tableSize _ | .elemDrop _ | .memorySize | .dataDrop _ => 0
  | .refIsNull | .tableGet _ | .memoryGrow => 1
  | .tableSet _ | .tableGrow _ => 2
  | .tableFill _ | .tableCopy .. | .tableInit .. | .memoryFill | .memoryCopy | .memoryInit _ => 3

theorem Instruction.arity_le_three (op : Instruction) : op.arity ≤ 3 := by
  cases op <;> simp [Instruction.arity]

end Exec.Abs.Stateful
