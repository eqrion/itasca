import Exec.Code.Local.Source.SourceExecutableTables
import Exec.Code.Local.Lowering.Simd.SimdSourceSignature
namespace Exec.Code.SourceExecutable
open Aeneas Aeneas.Std Itasca

def TokenWasm2 : Wasm2.Token → Prop
  | .plain source => Abs.BinaryInstr source
  | _ => True

theorem stateful (op : Abs.Stateful.Instruction) : Abs.BinaryInstr op.source :=
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
    Abs.BinaryInstr source := by
  cases encoded with
  | refNull type => exact stateful (.refNull _)
  | refIsNull => exact stateful .refIsNull
  | refFunc index _ => exact stateful (.refFunc index.val)
  | selectTyped => exact .typed_select _
  | tableGet index _ => exact stateful (.tableGet index.val)
  | tableSet index _ => exact stateful (.tableSet index.val)
  | callIndirect => exact .call_indirect _ _

theorem bulk {opcode source bytes} (encoded : Wasm2.BulkBinary.Immediate opcode source bytes) :
    Abs.BinaryInstr source := by
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
    Abs.BinaryInstr source := by
  apply Abs.BinaryInstr.simd
  cases encoded with
  | pure _ _ meaning => exact .pure (pure_source_signature meaning)
  | lane _ op lane _ => exact .pure (lane_source_signature op _)
  | memory _ op arg _ _ _ _ => exact .memory (memory_source_signature op _ _)
  | memoryLane _ op arg lane _ _ _ _ => exact .memory (memory_source_signature op _ _)
  | constant => exact .constant _
  | shuffle => with_unfolding_all exact Abs.SimdInstr.pure (.shuffle _ _)

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
end Exec.Code.SourceExecutable
