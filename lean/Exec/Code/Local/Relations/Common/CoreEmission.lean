import Exec.Code.Local.Control.Common.StructuredCode
import Exec.Code.Local.Relations.Global.GlobalLowering
import Exec.Code.Local.Relations.Common.SelectLowering
import Exec.Code.Local.Relations.Memory.MemoryOpcode
namespace Exec.Code
open Aeneas.Std

/-- Scalar mutable instructions retain their source module typing context.
The relation fixes syntax, operand layout and emitted bytecode only. -/
inductive CoreEmission (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | pure {before instruction emitted after}
      (emission : LinearEmission C.LOCALS before instruction emitted after) :
      CoreEmission C before instruction emitted after
  | float32 (stack) (dst bits : U32)
      (slot : dst.val = slots C.LOCALS + slots stack) :
      CoreEmission C stack (.CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 bits.val)))
        [.Const32 dst bits] (stack ++ [.F32])
  | float64 (stack) (dst : U32) (bits : U64)
      (slot : dst.val = slots C.LOCALS + slots stack) :
      CoreEmission C stack (.CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 bits.val)))
        [.Const64 dst bits] (stack ++ [.F64])
  | select (stack) (ty : valtype) (left right condition : U32)
      (leftSlot : left.val = slots C.LOCALS + slots stack)
      (rightSlot : right.val = left.val + width ty)
      (conditionSlot : condition.val = right.val + width ty) :
      CoreEmission C (stack ++ [ty, ty, .I32]) (.SELECT none)
        [selectInstruction (decide (width ty = 2)) left right condition] (stack ++ [ty])
  | globalGet (stack) (mutability : «mut») (ty : valtype) (index dst : U32)
      (globalType : C.GLOBALS[index.val]? = some (.mk_globaltype mutability ty))
      (slot : dst.val = slots C.LOCALS + slots stack) :
      CoreEmission C stack (.GLOBAL_GET (.mk_uN index.val))
        [globalGetInstruction (decide (width ty = 2)) dst index] (stack ++ [ty])
  | globalSet (stack) (ty : valtype) (index src : U32)
      (globalType : C.GLOBALS[index.val]? = some (.mk_globaltype (some .MUT) ty))
      (slot : src.val = slots C.LOCALS + slots stack) :
      CoreEmission C (stack ++ [ty]) (.GLOBAL_SET (.mk_uN index.val))
        [globalSetInstruction (decide (width ty = 2)) src index] stack
  | load (stack) (op : Abs.Memory.Load) (argument : memarg) (address offset : U32)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (sourceOffset : argument.OFFSET = .mk_uN offset.val)
      (slot : address.val = slots C.LOCALS + slots stack) :
      CoreEmission C (stack ++ [.I32]) (op.source argument)
        [memoryLoadInstruction op address address offset] (stack ++ [valtype_numtype op.type])
  | store (stack) (op : Abs.Memory.Store) (argument : memarg) (address value offset : U32)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (sourceOffset : argument.OFFSET = .mk_uN offset.val)
      (addressSlot : address.val = slots C.LOCALS + slots stack)
      (valueSlot : value.val = address.val + 1) :
      CoreEmission C (stack ++ [.I32, valtype_numtype op.type]) (op.source argument)
        [memoryStoreInstruction op address value offset] stack

theorem CoreEmission.length_le_one {C before instruction emitted after}
    (emission : CoreEmission C before instruction emitted after) : emitted.length ≤ 1 := by
  cases emission with
  | pure h => exact h.length_le_one
  | _ => simp

abbrev CoreCodeRel (C : context) (returns : List valtype) :=
  StructuredCode (CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS

theorem CodeRel.core {C : context} {returns code labels stack source pc next final}
    (relation : CodeRel C.TYPES C.FUNCS returns C.LOCALS code labels stack source pc next final) :
    CoreCodeRel C returns code labels stack source pc next final :=
  (StructuredCode.of_legacy relation).map_emission (fun _ _ _ _ h => .pure h)
end Exec.Code
