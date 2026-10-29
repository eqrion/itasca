import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.SourceMachine.Numeric.Decode

/-!
Scalar-emission inversion for floating-point constants.

Main declarations: `linear_emission_not_float` and `scalar_emission_float64_inv`. A direct consumer is `Interp.Machine.Constants.FloatConstant`.
-/

namespace Itasca.Runtime.Interp.FloatConstant
open Aeneas Aeneas.Std SpecExt

theorem linear_emission_not_float {locals before after emitted} (ty : Fnn) (value : fN)
    (emission : Compiler.LinearEmission locals before (.CONST (numtype_Fnn ty) (.mk_num__1 ty value)) emitted after) : False := by
  generalize equality : instr.CONST (numtype_Fnn ty) (.mk_num__1 ty value) = instruction at emission
  cases emission with
  | binary stack type op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    cases ty <;> simp [SourceMachine.Numeric.decodeInstruction,numtype_Fnn] at decoded
  | _ => cases ty <;> cases equality

theorem scalar_emission_float32_inv {C before after emitted} (value : fN)
    (emission : Compiler.ScalarEmission C before (.CONST .F32 (.mk_num__1 .F32 value)) emitted after) :
    ∃ dst bits, emitted = [.Const32 dst bits] ∧ after = before ++ [.F32] ∧
      value = Builtins.floatOfBits 32 bits.val ∧ dst.val = Compiler.slots C.LOCALS + Compiler.slots before := by
  generalize equality : instr.CONST .F32 (.mk_num__1 .F32 value) = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linear_emission_not_float .F32 value pure)
  | float32 stack dst bits slot =>
    cases equality
    exact ⟨dst,bits,rfl,rfl,rfl,slot⟩
  | load => simp [SourceMachine.Memory.Load.source] at equality
  | store => simp [SourceMachine.Memory.Store.source] at equality
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => cases equality

theorem scalar_emission_float64_inv {C before after emitted} (value : fN)
    (emission : Compiler.ScalarEmission C before (.CONST .F64 (.mk_num__1 .F64 value)) emitted after) :
    ∃ dst bits, emitted = [.Const64 dst bits] ∧ after = before ++ [.F64] ∧
      value = Builtins.floatOfBits 64 bits.val ∧ dst.val = Compiler.slots C.LOCALS + Compiler.slots before := by
  generalize equality : instr.CONST .F64 (.mk_num__1 .F64 value) = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linear_emission_not_float .F64 value pure)
  | float64 stack dst bits slot =>
    cases equality
    exact ⟨dst,bits,rfl,rfl,rfl,slot⟩
  | load => simp [SourceMachine.Memory.Load.source] at equality
  | store => simp [SourceMachine.Memory.Store.source] at equality
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => cases equality

end Itasca.Runtime.Interp.FloatConstant
