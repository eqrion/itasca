import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdLowering
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Binary.Wasm2.Simd

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca.Wasm2.Simd

/-- Source syntax and immediate fields retained by a SIMD metadata entry.
The opcode meanings are the independent binary-decoding tables. -/
inductive SimdImmediateMeaning (C : context) : U32 → runtime.bytecode.SimdImmediate →
    List valtype → instr → List valtype → Prop where
  | pure (opcode : U32) (immediate : runtime.bytecode.SimdImmediate) (op : Operation)
      (meaning : pureMeaning opcode.val = some op) :
      SimdImmediateMeaning C opcode immediate op.signature.inputs op.instruction op.signature.outputs
  | lane (opcode : U32) (immediate : runtime.bytecode.SimdImmediate) (op : LaneOperation)
      (meaning : laneMeaning opcode.val = some op) (lane : U8)
      (position : immediate.lane.val = lane.val) :
      SimdImmediateMeaning C opcode immediate op.inputs (op.instruction (.mk_uN lane.val)) op.outputs
  | memory (opcode : U32) (immediate : runtime.bytecode.SimdImmediate) (op : MemoryOperation)
      (meaning : memoryMeaning opcode.val = some op) (argument : memarg) (lane : U8)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (offset : argument.OFFSET = .mk_uN immediate.offset.val)
      (position : op.laneCount ≠ 0 → immediate.lane.val = lane.val) :
      SimdImmediateMeaning C opcode immediate op.inputs (op.instruction argument (.mk_uN lane.val)) op.outputs
  | shuffle (immediate : runtime.bytecode.SimdImmediate) (low high : U64)
      (bits : immediate.bits.val = low.val + high.val * 2^64) :
      SimdImmediateMeaning C 13#u32 immediate [.V128,.V128] (shuffle low high) [.V128]

/-- Exact SIMD instruction, slot, and function-local metadata correspondence.
Execution correctness and source typing are established separately. -/
inductive SimdEmission (immediates : List runtime.bytecode.SimdImmediate) (constants : List U128)
    (C : context) : List valtype → instr → List Bytecode → List valtype → Prop where
  | instruction (front input output : List valtype) (source : instr)
      (opcode operand entry : U32) (immediate : runtime.bytecode.SimdImmediate) (instruction : Bytecode)
      (meaning : SimdImmediateMeaning C opcode immediate input source output)
      (metadata : immediates[entry.val]? = some immediate)
      (constructed : runtime.bytecode.Instr.make_simd opcode operand operand entry = .ok (some instruction))
      (position : operand.val = slots C.LOCALS + slots front) :
      SimdEmission immediates constants C (front ++ input) source [instruction] (front ++ output)
  | constant (front : List valtype) (bits : U128) (dst entry : U32)
      (metadata : constants[entry.val]? = some bits)
      (position : dst.val = slots C.LOCALS + slots front) :
      SimdEmission immediates constants C front (.VCONST .V128 (.mk_uN bits.val))
        [.ConstV128 dst entry] (front ++ [.V128])

theorem SimdEmission.length_one {immediates constants C before source code after}
    (emission : SimdEmission immediates constants C before source code after) : code.length = 1 := by
  cases emission <;> rfl

theorem SimdEmission.append_tables {immediates constants C before source code after}
    (emission : SimdEmission immediates constants C before source code after)
    (extraImmediates : List runtime.bytecode.SimdImmediate) (extraConstants : List U128) :
    SimdEmission (immediates ++ extraImmediates) (constants ++ extraConstants) C before source code after := by
  cases emission with
  | instruction front input output source opcode operand entry immediate instruction meaning metadata constructed position =>
    apply SimdEmission.instruction front input output source opcode operand entry immediate instruction meaning _ constructed position
    have bound := (List.getElem?_eq_some_iff.mp metadata).1
    simpa [List.getElem?_append,bound] using metadata
  | constant front bits dst entry metadata position =>
    apply SimdEmission.constant _ bits dst entry _ position
    have bound := (List.getElem?_eq_some_iff.mp metadata).1
    simpa [List.getElem?_append,bound] using metadata

theorem SimdImmediateMeaning.context {C D opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (memories : C.MEMS = D.MEMS) :
    SimdImmediateMeaning D opcode immediate input source output := by
  cases meaning with
  | pure opcode immediate op meaning => exact .pure opcode immediate op meaning
  | lane opcode immediate op meaning lane position => exact .lane opcode immediate op meaning lane position
  | memory opcode immediate op meaning argument lane memory available offset position =>
    exact .memory opcode immediate op meaning argument lane memory (memories ▸ available) offset position
  | shuffle immediate low high bits => exact .shuffle immediate low high bits

theorem SimdEmission.context {immediates constants C D before source code after}
    (emission : SimdEmission immediates constants C before source code after)
    (memories : C.MEMS = D.MEMS) (locals : C.LOCALS = D.LOCALS) :
    SimdEmission immediates constants D before source code after := by
  cases emission with
  | instruction front input output source opcode operand entry immediate instruction meaning metadata constructed position =>
    exact .instruction front input output source opcode operand entry immediate instruction
      (meaning.context memories) metadata constructed (locals ▸ position)
  | constant front bits dst entry metadata position =>
    exact .constant _ bits dst entry metadata (locals ▸ position)

end Itasca.Runtime.Code
