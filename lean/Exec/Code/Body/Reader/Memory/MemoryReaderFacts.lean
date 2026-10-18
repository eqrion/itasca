import Exec.Code.Local.Relations.Memory.MemoryOpcode
import Exec.Code.Body.Reader.Memory.ReaderMemory
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

def memoryRawType : numtype → types.ValueType
  | .I32 => .I32 | .I64 => .I64 | .F32 => .F32 | .F64 => .F64

def memoryNatural : numtype → U32
  | .I32 | .F32 => 2#u32 | .I64 | .F64 => 3#u32

def memoryPackedNatural {ty} : Abs.Memory.PackedWidth ty → U32
  | .byte => 0#u32 | .half => 1#u32 | .word => 2#u32

def memoryLoadMeaning : Abs.Memory.Load → MemoryMeaning.Operation
  | .full ty => MemoryMeaning.fullLoad (memoryRawType ty) ty (memoryNatural ty)
  | .packed ty width sign => MemoryMeaning.packedLoad (memoryRawType (numtype_Inn ty)) ty width.bits sign (memoryPackedNatural width)

def memoryStoreMeaning : Abs.Memory.Store → MemoryMeaning.Operation
  | .full ty => MemoryMeaning.fullStore (memoryRawType ty) ty (memoryNatural ty)
  | .packed ty width => MemoryMeaning.packedStore (memoryRawType (numtype_Inn ty)) ty width.bits (memoryPackedNatural width)

@[simp] theorem memoryRawType_translate (ty : numtype) : Translate.valueType (memoryRawType ty) = valtype_numtype ty := by cases ty <;> rfl

 theorem memory_load_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Abs.Memory.Load) (arg : code.MemArg) :
    MemoryMeaning.opcodeMeaning (UScalar.cast .U8 (memoryLoadOpcode op)) = some (memoryLoadMeaning op) ∧
    (memoryLoadMeaning op).store = false ∧
    (memoryLoadMeaning op).ty = memoryRawType op.type ∧
    (memoryLoadMeaning op).op arg = op.source (MemoryMeaning.memArg arg) ∧
    code.visit_memory (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler state (UScalar.cast .U8 (memoryLoadOpcode op)) arg =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) arg.offset arg.align 0#u128 ∧
    (UScalar.cast .U8 (memoryLoadOpcode op)).val ∉ Wasm2.controlOpcodes ∧
    (UScalar.cast .U8 (memoryLoadOpcode op)).val ∉ [28,37,38,208,209,210,252,253] ∧
    Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (memoryLoadOpcode op)) = none ∧
    UScalar.cast .U8 (memoryLoadOpcode op) ≠ code.OP_MISC_PREFIX := by
  cases op with
  | full ty => cases ty <;> refine ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,?_⟩ <;> simp only [global_simps] <;> decide
  | packed ty width sign => cases ty <;> cases width <;> cases sign <;>
      refine ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,?_⟩ <;> simp only [global_simps] <;> decide

 theorem memory_store_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Abs.Memory.Store) (arg : code.MemArg) :
    MemoryMeaning.opcodeMeaning (UScalar.cast .U8 (memoryStoreOpcode op)) = some (memoryStoreMeaning op) ∧
    (memoryStoreMeaning op).store = true ∧
    (memoryStoreMeaning op).ty = memoryRawType op.type ∧
    (memoryStoreMeaning op).op arg = op.source (MemoryMeaning.memArg arg) ∧
    code.visit_memory (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler state (UScalar.cast .U8 (memoryStoreOpcode op)) arg =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) arg.offset arg.align 0#u128 ∧
    (UScalar.cast .U8 (memoryStoreOpcode op)).val ∉ Wasm2.controlOpcodes ∧
    (UScalar.cast .U8 (memoryStoreOpcode op)).val ∉ [28,37,38,208,209,210,252,253] ∧
    Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (memoryStoreOpcode op)) = none ∧
    UScalar.cast .U8 (memoryStoreOpcode op) ≠ code.OP_MISC_PREFIX := by
  cases op with
  | full ty => cases ty <;> refine ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,?_⟩ <;> simp only [global_simps] <;> decide
  | packed ty width => cases ty <;> cases width <;>
      refine ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,?_⟩ <;> simp only [global_simps] <;> decide
end Exec.Code
