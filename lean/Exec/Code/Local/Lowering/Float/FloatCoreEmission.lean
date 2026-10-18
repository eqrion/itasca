import Exec.Code.Local.Relations.Common.CoreEmission
import Exec.Code.Local.Lowering.Float.FloatOpcode
namespace Exec.Code
open Aeneas.Std

/-- An isolated extension of the contextual emission certificate. Its float
constructor records only exact syntax, slot layout and emitted bytecode. -/
inductive FloatCoreEmission (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | core {before instruction emitted after}
      (emission : CoreEmission C before instruction emitted after) :
      FloatCoreEmission C before instruction emitted after
  | scalar (stack : List valtype) (op : Abs.Float.Instruction) (left right : U32)
      (leftSlot : left.val = slots C.LOCALS + slots stack)
      (rightSlot : right.val = left.val + (op.arity - 1)) :
      FloatCoreEmission C (stack ++ List.replicate op.arity (valtype_numtype op.input))
        op.source [floatInstruction op left left right] (stack ++ [valtype_numtype op.output])

theorem FloatCoreEmission.length_le_one {C before instruction emitted after}
    (emission : FloatCoreEmission C before instruction emitted after) : emitted.length ≤ 1 := by
  cases emission with
  | core h => exact h.length_le_one
  | scalar => simp

abbrev FloatCoreCodeRel (C : context) (returns : List valtype) :=
  StructuredCode (FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS

theorem CoreCodeRel.float_core {C : context} {returns code labels stack source pc next final}
    (relation : CoreCodeRel C returns code labels stack source pc next final) :
    FloatCoreCodeRel C returns code labels stack source pc next final :=
  relation.map_emission (fun _ _ _ _ h => .core h)
end Exec.Code
