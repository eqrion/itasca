import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Relations.ConstCodePoint
namespace Itasca.Runtime.Interp.IntegerConstant
open Aeneas Aeneas.Std SpecExt

theorem scalarEmission_integer32_inv {C before after emitted} (value : U32)
    (emission : Code.ScalarEmission C before (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))) emitted after) :
    ∃ dst bits, emitted = [.Const32 dst bits] ∧ after = before ++ [.I32] ∧
      value = bits ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    obtain ⟨dst,emitted,result,position⟩ := linearEmission_const32_inv value pure
    exact ⟨dst,value,emitted,result,rfl,position⟩
  | load => simp [Abs.Memory.Load.source] at equality
  | store => simp [Abs.Memory.Store.source] at equality
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => cases equality

theorem scalarEmission_integer64_inv {C before after emitted} (value : U64)
    (emission : Code.ScalarEmission C before (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))) emitted after) :
    ∃ dst bits, emitted = [.Const64 dst bits] ∧ after = before ++ [.I64] ∧
      value = bits ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    obtain ⟨dst,emitted,result,position⟩ := linearEmission_const64_inv value pure
    exact ⟨dst,value,emitted,result,rfl,position⟩
  | load => simp [Abs.Memory.Load.source] at equality
  | store => simp [Abs.Memory.Store.source] at equality
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => cases equality

end Itasca.Runtime.Interp.IntegerConstant
