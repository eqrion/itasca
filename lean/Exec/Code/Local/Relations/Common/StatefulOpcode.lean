import Exec.Abs.Stateful.Descriptor
import Itasca.Generated.Types

namespace Itasca.Runtime.Code
open Aeneas.Std

/-- Expanded opcodes use 0x100 plus the misc-prefix subopcode. -/
def statefulOpcode : Abs.Stateful.Instruction → U16
  | .refNull _ => 208#u16
  | .refFunc _ => 210#u16
  | .refIsNull => 209#u16
  | .tableGet _ => 37#u16
  | .tableSet _ => 38#u16
  | .tableSize _ => 272#u16
  | .tableGrow _ => 271#u16
  | .tableFill _ => 273#u16
  | .tableCopy .. => 270#u16
  | .tableInit .. => 268#u16
  | .elemDrop _ => 269#u16
  | .memorySize => 63#u16
  | .memoryGrow => 64#u16
  | .memoryFill => 267#u16
  | .memoryCopy => 266#u16
  | .memoryInit _ => 264#u16
  | .dataDrop _ => 265#u16

/-- Callback arguments, including the reversed table.init pair order. -/
def statefulArguments : Abs.Stateful.Instruction → Nat × Nat
  | .refNull .FUNCREF => (0, 0)
  | .refNull .EXTERNREF => (1, 0)
  | .refFunc index | .tableGet index | .tableSet index | .tableSize index
    | .tableGrow index | .tableFill index | .elemDrop index | .memoryInit index
    | .dataDrop index => (index, 0)
  | .tableCopy destination source => (destination, source)
  | .tableInit table element => (element, table)
  | _ => (0, 0)

def StatefulArguments (op : Abs.Stateful.Instruction) (a b : U32) : Prop :=
  a.val = (statefulArguments op).1 ∧ b.val = (statefulArguments op).2

/-- Exact bytecode constructor. `first` starts the complete operand suffix;
`second` is the next scalar slot. `entry` indexes the retained pair table. -/
def statefulInstruction (op : Abs.Stateful.Instruction) (first second a entry : U32) :
    runtime.bytecode.Instr :=
  match op with
  | .refNull _ => .RefNull first
  | .refFunc _ => .RefFunc first a
  | .refIsNull => .RefIsNull first first
  | .tableGet _ => .TableGet first first a
  | .tableSet _ => .TableSet first second a
  | .tableSize _ => .TableSize first a
  | .tableGrow _ => .TableGrow first a
  | .tableFill _ => .TableFill first a
  | .tableCopy .. => .TableCopy first entry
  | .tableInit .. => .TableInit first entry
  | .elemDrop _ => .ElemDrop a
  | .memorySize => .MemorySize first
  | .memoryGrow => .MemoryGrow first
  | .memoryFill => .MemoryFill first
  | .memoryCopy => .MemoryCopy first
  | .memoryInit _ => .MemoryInit first a
  | .dataDrop _ => .DataDrop a

/-- Pair-table entries are function-local immutable compiler metadata. -/
def StatefulPair (pairs : List (U32 × U32)) (op : Abs.Stateful.Instruction)
    (a b entry : U32) : Prop :=
  match op with
  | .tableCopy .. | .tableInit .. => pairs[entry.val]? = some (a, b)
  | _ => True

end Itasca.Runtime.Code
