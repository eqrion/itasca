import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering
import Itasca.Runtime.Compiler.Local.Relations.Select.SelectLowering
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatOpcode

/-!
Scalar instructions, including those resolved against the module's globals and memory, with their source typing context. The relation fixes syntax, operand layout and emitted bytecode only.

Main declarations: `ScalarEmission`. A direct consumer is `Compiler.Local.Relations.Calls.IndirectCallEmission`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Scalar instructions, including those resolved against the module's globals and
memory, with their source typing context. The relation fixes syntax, operand layout
and emitted bytecode only. -/
inductive ScalarEmission (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | linear {before instruction emitted after}
      (emission : LinearEmission C.LOCALS before instruction emitted after) :
      ScalarEmission C before instruction emitted after
  | float32 (stack) (dst bits : U32)
      (slot : dst.val = slots C.LOCALS + slots stack) :
      ScalarEmission C stack (.CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 bits.val)))
        [.Const32 dst bits] (stack ++ [.F32])
  | float64 (stack) (dst : U32) (bits : U64)
      (slot : dst.val = slots C.LOCALS + slots stack) :
      ScalarEmission C stack (.CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 bits.val)))
        [.Const64 dst bits] (stack ++ [.F64])
  | select (stack) (ty : valtype) (left right condition : U32)
      (leftSlot : left.val = slots C.LOCALS + slots stack)
      (rightSlot : right.val = left.val + width ty)
      (conditionSlot : condition.val = right.val + width ty) :
      ScalarEmission C (stack ++ [ty, ty, .I32]) (.SELECT none)
        [selectInstruction (decide (width ty = 2)) left right condition] (stack ++ [ty])
  | globalGet (stack) (mutability : «mut») (ty : valtype) (index dst : U32)
      (globalType : C.GLOBALS[index.val]? = some (.mk_globaltype mutability ty))
      (slot : dst.val = slots C.LOCALS + slots stack) :
      ScalarEmission C stack (.GLOBAL_GET (.mk_uN index.val))
        [globalGetInstruction (decide (width ty = 2)) dst index] (stack ++ [ty])
  | globalSet (stack) (ty : valtype) (index src : U32)
      (globalType : C.GLOBALS[index.val]? = some (.mk_globaltype (some .MUT) ty))
      (slot : src.val = slots C.LOCALS + slots stack) :
      ScalarEmission C (stack ++ [ty]) (.GLOBAL_SET (.mk_uN index.val))
        [globalSetInstruction (decide (width ty = 2)) src index] stack
  | load (stack) (op : SourceMachine.Memory.Load) (argument : memarg) (address offset : U32)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (sourceOffset : argument.OFFSET = .mk_uN offset.val)
      (slot : address.val = slots C.LOCALS + slots stack) :
      ScalarEmission C (stack ++ [.I32]) (op.source argument)
        [memoryLoadInstruction op address address offset] (stack ++ [valtype_numtype op.type])
  | store (stack) (op : SourceMachine.Memory.Store) (argument : memarg) (address value offset : U32)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (sourceOffset : argument.OFFSET = .mk_uN offset.val)
      (addressSlot : address.val = slots C.LOCALS + slots stack)
      (valueSlot : value.val = address.val + 1) :
      ScalarEmission C (stack ++ [.I32, valtype_numtype op.type]) (op.source argument)
        [memoryStoreInstruction op address value offset] stack
  | float (stack : List valtype) (op : SourceMachine.Float.Instruction) (left right : U32)
      (leftSlot : left.val = slots C.LOCALS + slots stack)
      (rightSlot : right.val = left.val + (op.arity - 1)) :
      ScalarEmission C (stack ++ List.replicate op.arity (valtype_numtype op.input))
        op.source [floatInstruction op left left right] (stack ++ [valtype_numtype op.output])

end Itasca.Runtime.Compiler
