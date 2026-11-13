import Itasca.Runtime.SourceMachine.Decode

/-!
Sections, each formerly its own module: Descriptor, Signature.
-/

/-! ## Descriptor -/

section

namespace Itasca.Runtime.SourceMachine.Stateful

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

end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Signature -/

section

namespace Itasca.Runtime.SourceMachine.Stateful

/-- Canonical source index spaces determine the operand/result types. -/
inductive Signature (C : context) : Instruction → List valtype → List valtype → Prop where
  | refNull (type) : Signature C (.refNull type) [] [valtype_reftype type]
  | refFunc (index) (type : functype) (found : C.FUNCS[index]? = some type) :
      Signature C (.refFunc index) [] [.FUNCREF]
  | refIsNull (type) : Signature C .refIsNull [valtype_reftype type] [.I32]
  | tableGet (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableGet index) [.I32] [valtype_reftype type]
  | tableSet (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableSet index) [.I32, valtype_reftype type] []
  | tableSize (index) (type : tabletype) (found : C.TABLES[index]? = some type) :
      Signature C (.tableSize index) [] [.I32]
  | tableGrow (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableGrow index) [valtype_reftype type, .I32] [.I32]
  | tableFill (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableFill index) [.I32, valtype_reftype type, .I32] []
  | tableCopy (destination source) (type) (destinationBounds sourceBounds)
      (destinationFound : C.TABLES[destination]? = some (.mk_tabletype destinationBounds type))
      (sourceFound : C.TABLES[source]? = some (.mk_tabletype sourceBounds type)) :
      Signature C (.tableCopy destination source) [.I32, .I32, .I32] []
  | tableInit (table element) (type) (bounds)
      (tableFound : C.TABLES[table]? = some (.mk_tabletype bounds type))
      (elementFound : C.ELEMS[element]? = some type) :
      Signature C (.tableInit table element) [.I32, .I32, .I32] []
  | elemDrop (index) (type : reftype) (found : C.ELEMS[index]? = some type) :
      Signature C (.elemDrop index) [] []
  | memorySize (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memorySize [] [.I32]
  | memoryGrow (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryGrow [.I32] [.I32]
  | memoryFill (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryFill [.I32, .I32, .I32] []
  | memoryCopy (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryCopy [.I32, .I32, .I32] []
  | memoryInit (index) (type : memtype) (found : C.MEMS[0]? = some type)
      (dataFound : C.DATAS[index]? = some .OK) :
      Signature C (.memoryInit index) [.I32, .I32, .I32] []
  | dataDrop (index) (found : C.DATAS[index]? = some .OK) :
      Signature C (.dataDrop index) [] []

theorem Signature.input_length {C op input output} (signature : Signature C op input output) :
    input.length = op.arity := by
  cases signature <;> rfl

private theorem reference_scalar (type : reftype) : valtype_reftype type ≠ valtype.V128 := by
  cases type <;> decide

theorem Signature.inputs_scalar {C op input output} (signature : Signature C op input output) :
    ∀ type ∈ input, type ≠ valtype.V128 := by
  cases signature <;> simp_all [reference_scalar]

end Itasca.Runtime.SourceMachine.Stateful

end
