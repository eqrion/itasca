import Itasca.Runtime.SourceMachine.BinaryInstr
import Itasca.Binary.Wasm2.Encoding
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdSourceSignature

/-!
Independent instruction encodings belong to the executable source grammar. TokenWasm2 classification covers each profile's immediate encodings before lifting through token consumption and whole bodies.
-/

/-! ## Source Executable Tables -/

section

namespace Itasca.Runtime.Compiler.SourceExecutable
open Aeneas Aeneas.Std Itasca

theorem integer (op : SourceMachine.Numeric.Instruction) : SourceMachine.BinaryInstr op.source := .numeric op
theorem floating (op : SourceMachine.Float.Instruction) : SourceMachine.BinaryInstr op.source := .float op

theorem numeric {opcode operation} (meaning : Numeric.opcodeMeaning opcode = some operation) :
    SourceMachine.BinaryInstr operation.instruction := by
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact integer (.eqz .I32)
  · exact integer (.compare .I32 (.EQ))
  · exact integer (.compare .I32 (.NE))
  · exact integer (.compare .I32 (.LT .S))
  · exact integer (.compare .I32 (.LT .U))
  · exact integer (.compare .I32 (.GT .S))
  · exact integer (.compare .I32 (.GT .U))
  · exact integer (.compare .I32 (.LE .S))
  · exact integer (.compare .I32 (.LE .U))
  · exact integer (.compare .I32 (.GE .S))
  · exact integer (.compare .I32 (.GE .U))
  · exact integer (.eqz .I64)
  · exact integer (.compare .I64 (.EQ))
  · exact integer (.compare .I64 (.NE))
  · exact integer (.compare .I64 (.LT .S))
  · exact integer (.compare .I64 (.LT .U))
  · exact integer (.compare .I64 (.GT .S))
  · exact integer (.compare .I64 (.GT .U))
  · exact integer (.compare .I64 (.LE .S))
  · exact integer (.compare .I64 (.LE .U))
  · exact integer (.compare .I64 (.GE .S))
  · exact integer (.compare .I64 (.GE .U))
  · exact floating (.compare .F32 .EQ)
  · exact floating (.compare .F32 .NE)
  · exact floating (.compare .F32 .LT)
  · exact floating (.compare .F32 .GT)
  · exact floating (.compare .F32 .LE)
  · exact floating (.compare .F32 .GE)
  · exact floating (.compare .F64 .EQ)
  · exact floating (.compare .F64 .NE)
  · exact floating (.compare .F64 .LT)
  · exact floating (.compare .F64 .GT)
  · exact floating (.compare .F64 .LE)
  · exact floating (.compare .F64 .GE)
  · exact integer (.unary .I32 .clz)
  · exact integer (.unary .I32 .ctz)
  · exact integer (.unary .I32 .popcnt)
  · exact integer (.binary .I32 (.ADD))
  · exact integer (.binary .I32 (.SUB))
  · exact integer (.binary .I32 (.MUL))
  · exact integer (.binary .I32 (.DIV .S))
  · exact integer (.binary .I32 (.DIV .U))
  · exact integer (.binary .I32 (.REM .S))
  · exact integer (.binary .I32 (.REM .U))
  · exact integer (.binary .I32 (.AND))
  · exact integer (.binary .I32 (.OR))
  · exact integer (.binary .I32 (.XOR))
  · exact integer (.binary .I32 (.SHL))
  · exact integer (.binary .I32 (.SHR .S))
  · exact integer (.binary .I32 (.SHR .U))
  · exact integer (.binary .I32 (.ROTL))
  · exact integer (.binary .I32 (.ROTR))
  · exact integer (.unary .I64 .clz)
  · exact integer (.unary .I64 .ctz)
  · exact integer (.unary .I64 .popcnt)
  · exact integer (.binary .I64 (.ADD))
  · exact integer (.binary .I64 (.SUB))
  · exact integer (.binary .I64 (.MUL))
  · exact integer (.binary .I64 (.DIV .S))
  · exact integer (.binary .I64 (.DIV .U))
  · exact integer (.binary .I64 (.REM .S))
  · exact integer (.binary .I64 (.REM .U))
  · exact integer (.binary .I64 (.AND))
  · exact integer (.binary .I64 (.OR))
  · exact integer (.binary .I64 (.XOR))
  · exact integer (.binary .I64 (.SHL))
  · exact integer (.binary .I64 (.SHR .S))
  · exact integer (.binary .I64 (.SHR .U))
  · exact integer (.binary .I64 (.ROTL))
  · exact integer (.binary .I64 (.ROTR))
  · exact floating (.unary .F32 .ABS)
  · exact floating (.unary .F32 .NEG)
  · exact floating (.unary .F32 .CEIL)
  · exact floating (.unary .F32 .FLOOR)
  · exact floating (.unary .F32 .TRUNC)
  · exact floating (.unary .F32 .NEAREST)
  · exact floating (.unary .F32 .SQRT)
  · exact floating (.binary .F32 .ADD)
  · exact floating (.binary .F32 .SUB)
  · exact floating (.binary .F32 .MUL)
  · exact floating (.binary .F32 .DIV)
  · exact floating (.binary .F32 .MIN)
  · exact floating (.binary .F32 .MAX)
  · exact floating (.binary .F32 .COPYSIGN)
  · exact floating (.unary .F64 .ABS)
  · exact floating (.unary .F64 .NEG)
  · exact floating (.unary .F64 .CEIL)
  · exact floating (.unary .F64 .FLOOR)
  · exact floating (.unary .F64 .TRUNC)
  · exact floating (.unary .F64 .NEAREST)
  · exact floating (.unary .F64 .SQRT)
  · exact floating (.binary .F64 .ADD)
  · exact floating (.binary .F64 .SUB)
  · exact floating (.binary .F64 .MUL)
  · exact floating (.binary .F64 .DIV)
  · exact floating (.binary .F64 .MIN)
  · exact floating (.binary .F64 .MAX)
  · exact floating (.binary .F64 .COPYSIGN)
  · exact integer (.conversion .wrap)
  · exact floating (.truncate .F32 .I32 .S false)
  · exact floating (.truncate .F32 .I32 .U false)
  · exact floating (.truncate .F64 .I32 .S false)
  · exact floating (.truncate .F64 .I32 .U false)
  · exact integer (.conversion .extendSigned)
  · exact integer (.conversion .extendUnsigned)
  · exact floating (.truncate .F32 .I64 .S false)
  · exact floating (.truncate .F32 .I64 .U false)
  · exact floating (.truncate .F64 .I64 .S false)
  · exact floating (.truncate .F64 .I64 .U false)
  · exact floating (.convert .I32 .F32 .S)
  · exact floating (.convert .I32 .F32 .U)
  · exact floating (.convert .I64 .F32 .S)
  · exact floating (.convert .I64 .F32 .U)
  · exact floating (.demote)
  · exact floating (.convert .I32 .F64 .S)
  · exact floating (.convert .I32 .F64 .U)
  · exact floating (.convert .I64 .F64 .S)
  · exact floating (.convert .I64 .F64 .U)
  · exact floating (.promote)
  · exact floating (.reinterpretFloat .F32)
  · exact floating (.reinterpretFloat .F64)
  · exact floating (.reinterpretInt .I32)
  · exact floating (.reinterpretInt .I64)

theorem sign {opcode operation} (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation) :
    SourceMachine.BinaryInstr operation.instruction := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact integer (.unary .I32 .extend8)
  · exact integer (.unary .I32 .extend16)
  · exact integer (.unary .I64 .extend8)
  · exact integer (.unary .I64 .extend16)
  · exact integer (.unary .I64 .extend32)

theorem saturating {opcode operation} (meaning : Wasm2.NumericExtensions.saturatingMeaning opcode = some operation) :
    SourceMachine.BinaryInstr operation.instruction := by
  unfold Wasm2.NumericExtensions.saturatingMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact floating (.truncate .F32 .I32 .S true)
  · exact floating (.truncate .F32 .I32 .U true)
  · exact floating (.truncate .F64 .I32 .S true)
  · exact floating (.truncate .F64 .I32 .U true)
  · exact floating (.truncate .F32 .I64 .S true)
  · exact floating (.truncate .F32 .I64 .U true)
  · exact floating (.truncate .F64 .I64 .S true)
  · exact floating (.truncate .F64 .I64 .U true)

theorem memory {opcode operation} (arg : code.MemArg)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation) :
    SourceMachine.BinaryInstr (operation.op arg) := by
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact .load (.full .I32) _
  · exact .load (.full .I64) _
  · exact .load (.full .F32) _
  · exact .load (.full .F64) _
  · exact .load (.packed .I32 .byte .S) _
  · exact .load (.packed .I32 .byte .U) _
  · exact .load (.packed .I32 .half .S) _
  · exact .load (.packed .I32 .half .U) _
  · exact .load (.packed .I64 .byte .S) _
  · exact .load (.packed .I64 .byte .U) _
  · exact .load (.packed .I64 .half .S) _
  · exact .load (.packed .I64 .half .U) _
  · exact .load (.packed .I64 .word .S) _
  · exact .load (.packed .I64 .word .U) _
  · exact .store (.full .I32) _
  · exact .store (.full .I64) _
  · exact .store (.full .F32) _
  · exact .store (.full .F64) _
  · exact .store (.packed .I32 .byte) _
  · exact .store (.packed .I32 .half) _
  · exact .store (.packed .I64 .byte) _
  · exact .store (.packed .I64 .half) _
  · exact .store (.packed .I64 .word) _
end Itasca.Runtime.Compiler.SourceExecutable

end

/-! ## Source Executable Immediate -/

section

namespace Itasca.Runtime.Compiler.SourceExecutable
open Aeneas Aeneas.Std Itasca

def TokenWasm2 : Wasm2.Token → Prop
  | .plain source => SourceMachine.BinaryInstr source
  | _ => True

theorem stateful (op : SourceMachine.Stateful.Instruction) : SourceMachine.BinaryInstr op.source :=
  .stateful op

theorem immediate_wasm1 {opcode token bytes} (encoded : Wasm1.Immediate opcode token bytes) :
    TokenWasm2 token := by
  cases encoded with
  | unreachable => exact .unreachable
  | nop => exact .nop
  | block | loop | if_ | else_ | end_ => trivial
  | br idx _ => exact .br _
  | brIf idx _ => exact .br_if _
  | brTable => exact .br_table _ _
  | return_ => exact .ret
  | call idx _ => exact .call _
  | callIndirect => exact .call_indirect _ _
  | drop => exact .drop
  | select => exact .select
  | localGet => exact .local_get _
  | localSet => exact .local_set _
  | localTee => exact .local_tee _
  | globalGet => exact .global_get _
  | globalSet => exact .global_set _
  | memory opcode op arg meaning _ _ => exact memory arg meaning
  | memorySize => exact stateful .memorySize
  | memoryGrow => exact stateful .memoryGrow
  | i32Const => exact .const _ _
  | i64Const => exact .const _ _
  | f32Const => exact .const _ _
  | f64Const => exact .const _ _
  | numeric opcode operation meaning => exact numeric meaning

theorem reference {opcode source bytes} (encoded : Wasm2.ReferencesBinary.Immediate opcode source bytes) :
    SourceMachine.BinaryInstr source := by
  cases encoded with
  | refNull type => exact stateful (.refNull _)
  | refIsNull => exact stateful .refIsNull
  | refFunc index _ => exact stateful (.refFunc index.val)
  | selectTyped => exact .typed_select _
  | tableGet index _ => exact stateful (.tableGet index.val)
  | tableSet index _ => exact stateful (.tableSet index.val)
  | callIndirect => exact .call_indirect _ _

theorem bulk {opcode source bytes} (encoded : Wasm2.BulkBinary.Immediate opcode source bytes) :
    SourceMachine.BinaryInstr source := by
  cases encoded with
  | memoryInit index _ => exact stateful (.memoryInit index.val)
  | dataDrop index _ => exact stateful (.dataDrop index.val)
  | memoryCopy => exact stateful .memoryCopy
  | memoryFill => exact stateful .memoryFill
  | tableInit element table _ _ => exact stateful (.tableInit table.val element.val)
  | elemDrop index _ => exact stateful (.elemDrop index.val)
  | tableCopy destination source _ _ => exact stateful (.tableCopy destination.val source.val)
  | tableGrow index _ => exact stateful (.tableGrow index.val)
  | tableSize index _ => exact stateful (.tableSize index.val)
  | tableFill index _ => exact stateful (.tableFill index.val)

theorem simd {opcode source bytes} (encoded : Wasm2.Simd.Immediate opcode source bytes) :
    SourceMachine.BinaryInstr source := by
  apply SourceMachine.BinaryInstr.simd
  cases encoded with
  | pure _ _ meaning => exact .pure (pure_source_signature meaning)
  | lane _ op lane _ => exact .pure (lane_source_signature op _)
  | memory _ op arg _ _ _ _ => exact .memory (memory_source_signature op _ _)
  | memoryLane _ op arg lane _ _ _ _ => exact .memory (memory_source_signature op _ _)
  | constant => exact .constant _
  | shuffle => with_unfolding_all exact SourceMachine.SimdInstr.pure (.shuffle _ _)

theorem immediate_wasm2 {opcode token bytes} (encoded : Wasm2.Immediate opcode token bytes) :
    TokenWasm2 token := by
  cases encoded with
  | plain old => exact immediate_wasm1 old
  | signExtension _ _ meaning => exact sign meaning
  | saturating _ _ meaning _ => exact saturating meaning
  | reference encoded => exact reference encoded
  | bulk _ _ encoded => exact bulk encoded
  | simd _ _ encoded => exact simd encoded
  | block | loop | if_ | else_ | end_ => trivial
end Itasca.Runtime.Compiler.SourceExecutable

end

/-! ## Source Executable Body -/

section

namespace Itasca.Runtime.Compiler.SourceExecutable
open Aeneas Aeneas.Std Itasca

theorem token_wasm1 {token bytes} (encoded : Wasm1.TokenEncoding token bytes) : TokenWasm2 token := by
  obtain ⟨opcode, immediate, _, encoded⟩ := encoded
  exact immediate_wasm1 encoded

theorem token_wasm2 {token bytes} (encoded : Wasm2.TokenEncoding token bytes) : TokenWasm2 token := by
  obtain ⟨opcode, immediate, _, encoded⟩ := encoded
  exact immediate_wasm2 encoded

theorem consumed_wasm2 {data start tokens next} (encoded : Wasm2.Consumed data start tokens next) :
    Forall TokenWasm2 tokens := by
  induction encoded with
  | nil => simp [Forall]
  | snoc _ atToken ih =>
    obtain ⟨bytes, encoded, _⟩ := atToken
    simpa [Forall, or_imp, forall_and] using And.intro ih (token_wasm2 encoded)

theorem emits_wasm2 {tokens source} (emitted : Wasm2.Emits tokens source)
    (known : Forall TokenWasm2 tokens) : Forall SourceMachine.BinaryInstr source := by
  induction emitted with
  | nil => simp [Forall]
  | simple _ simple ih =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    cases simple
    simpa [Forall, or_imp, forall_and, TokenWasm2] using And.intro (ih known.1) (known.2 _ rfl)
  | block bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (SourceMachine.BinaryInstr.block _ _ hbody)
  | loop bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (SourceMachine.BinaryInstr.loop _ _ hbody)
  | ifElse bt _ _ _ ih yes no =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hyes := yes known.1.1.1.2
    have hno := no known.1.2
    have prior := ih known.1.1.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (SourceMachine.BinaryInstr.ifelse _ _ _ hyes hno)
  | ifEnd bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior
      (SourceMachine.BinaryInstr.ifelse _ _ [] hbody (by simp [Forall]))

theorem body_wasm2 {data source} (encoded : Wasm2.BodyEncoding data source) :
    Forall SourceMachine.BinaryInstr source := by
  obtain ⟨tokens, next, consumed, _, inner, rfl, emitted⟩ := encoded
  have known := consumed_wasm2 consumed
  exact emits_wasm2 emitted (fun token member => known token (List.mem_append_left _ member))
end Itasca.Runtime.Compiler.SourceExecutable

end
