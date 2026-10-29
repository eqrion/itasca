import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.ConstCodePoint

/-!
Scalar-emission inversion for integer constants.

Main declarations: `scalar_emission_integer32_inv` and `scalar_emission_integer64_inv`. A direct consumer is `Interp.Machine.Constants.IntegerConstant`.
-/

namespace Itasca.Runtime.Interp.IntegerConstant
open Aeneas Aeneas.Std SpecExt

theorem scalar_emission_integer32_inv {C before after emitted} (value : U32)
    (emission : Compiler.ScalarEmission C before (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))) emitted after) :
    ∃ dst bits, emitted = [.Const32 dst bits] ∧ after = before ++ [.I32] ∧
      value = bits ∧ dst.val = Compiler.slots C.LOCALS + Compiler.slots before := by
  generalize equality : instr.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    obtain ⟨dst,emitted,result,position⟩ := linear_emission_const32_inv value pure
    exact ⟨dst,value,emitted,result,rfl,position⟩
  | load => simp [SourceMachine.Memory.Load.source] at equality
  | store => simp [SourceMachine.Memory.Store.source] at equality
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => cases equality

theorem scalar_emission_integer64_inv {C before after emitted} (value : U64)
    (emission : Compiler.ScalarEmission C before (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))) emitted after) :
    ∃ dst bits, emitted = [.Const64 dst bits] ∧ after = before ++ [.I64] ∧
      value = bits ∧ dst.val = Compiler.slots C.LOCALS + Compiler.slots before := by
  generalize equality : instr.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    obtain ⟨dst,emitted,result,position⟩ := linear_emission_const64_inv value pure
    exact ⟨dst,value,emitted,result,rfl,position⟩
  | load => simp [SourceMachine.Memory.Load.source] at equality
  | store => simp [SourceMachine.Memory.Store.source] at equality
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => cases equality

end Itasca.Runtime.Interp.IntegerConstant
