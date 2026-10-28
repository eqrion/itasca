import Itasca.Runtime.Code.Local.Relations.Common.ScalarEmission
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Control.Common.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Abs.ModuleBindingsExtension
import Itasca.Runtime.Abs.Numeric.Decode
namespace Itasca.Runtime.Interp.FloatConstant
open Aeneas Aeneas.Std SpecExt

theorem linearEmission_not_float {locals before after emitted} (ty : Fnn) (value : fN)
    (emission : Code.LinearEmission locals before (.CONST (numtype_Fnn ty) (.mk_num__1 ty value)) emitted after) : False := by
  generalize equality : instr.CONST (numtype_Fnn ty) (.mk_num__1 ty value) = instruction at emission
  cases emission with
  | binary stack type op a b left right => cases op <;> simp [Code.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    cases ty <;> simp [Abs.Numeric.decodeInstruction,numtype_Fnn] at decoded
  | _ => cases ty <;> cases equality

theorem scalarEmission_float32_inv {C before after emitted} (value : fN)
    (emission : Code.ScalarEmission C before (.CONST .F32 (.mk_num__1 .F32 value)) emitted after) :
    ∃ dst bits, emitted = [.Const32 dst bits] ∧ after = before ++ [.F32] ∧
      value = Builtins.floatOfBits 32 bits.val ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.CONST .F32 (.mk_num__1 .F32 value) = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linearEmission_not_float .F32 value pure)
  | float32 stack dst bits slot =>
    cases equality
    exact ⟨dst,bits,rfl,rfl,rfl,slot⟩
  | load => simp [Abs.Memory.Load.source] at equality
  | store => simp [Abs.Memory.Store.source] at equality
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => cases equality

theorem scalarEmission_float64_inv {C before after emitted} (value : fN)
    (emission : Code.ScalarEmission C before (.CONST .F64 (.mk_num__1 .F64 value)) emitted after) :
    ∃ dst bits, emitted = [.Const64 dst bits] ∧ after = before ++ [.F64] ∧
      value = Builtins.floatOfBits 64 bits.val ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.CONST .F64 (.mk_num__1 .F64 value) = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linearEmission_not_float .F64 value pure)
  | float64 stack dst bits slot =>
    cases equality
    exact ⟨dst,bits,rfl,rfl,rfl,slot⟩
  | load => simp [Abs.Memory.Load.source] at equality
  | store => simp [Abs.Memory.Store.source] at equality
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => cases equality

end Itasca.Runtime.Interp.FloatConstant
