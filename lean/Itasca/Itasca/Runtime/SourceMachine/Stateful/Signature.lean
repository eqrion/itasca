import Itasca.Runtime.SourceMachine.Simulation

/-! ## Descriptor -/

section

namespace Itasca.SourceMachine.Stateful

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

theorem Instruction.arity_le_three (op : Instruction) : op.arity ≤ 3 := by
  cases op <;> simp [Instruction.arity]

end Itasca.SourceMachine.Stateful

end

/-! ## Signature -/

section

namespace Itasca.SourceMachine.Stateful

theorem Signature.input_length {C op input output} (signature : Signature C op input output) :
    input.length = op.arity := by
  cases signature <;> rfl

private theorem reference_scalar (type : reftype) : valtype_reftype type ≠ valtype.V128 := by
  cases type <;> decide

theorem Signature.inputs_scalar {C op input output} (signature : Signature C op input output) :
    ∀ type ∈ input, type ≠ valtype.V128 := by
  cases signature <;> simp_all [reference_scalar]

end Itasca.SourceMachine.Stateful

end
