import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Abs.Numeric.Decode
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem linearEmission_not_globalGet {locals before after emitted index}
    (emission : Code.LinearEmission locals before (.GLOBAL_GET index) emitted after) : False := by
  generalize equality : instr.GLOBAL_GET index = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Code.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem linearEmission_not_globalSet {locals before after emitted index}
    (emission : Code.LinearEmission locals before (.GLOBAL_SET index) emitted after) : False := by
  generalize equality : instr.GLOBAL_SET index = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Code.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem scalarEmission_globalGet_inv {C before after emitted} (index : Nat)
    (emission : Code.ScalarEmission C before (.GLOBAL_GET (.mk_uN index)) emitted after) :
    ∃ mutability ty idx dst, index = idx.val ∧
      C.GLOBALS[index]? = some (.mk_globaltype mutability ty) ∧
      emitted = [Code.globalGetInstruction (decide (Code.width ty = 2)) dst idx] ∧
      after = before ++ [ty] ∧ dst.val = Code.slots C.LOCALS + Code.slots before := by
  generalize equality : instr.GLOBAL_GET (.mk_uN index) = instruction at emission
  cases emission with
  | linear pure => rw [←equality] at pure; exact False.elim (linearEmission_not_globalGet pure)
  | globalGet stack mutability ty idx dst lookup position =>
    cases equality
    exact ⟨mutability,ty,idx,dst,rfl,lookup,rfl,rfl,position⟩
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality

theorem scalarEmission_globalSet_inv {C before after emitted} (index : Nat)
    (emission : Code.ScalarEmission C before (.GLOBAL_SET (.mk_uN index)) emitted after) :
    ∃ front ty idx src, index = idx.val ∧ before = front ++ [ty] ∧
      C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) ∧
      emitted = [Code.globalSetInstruction (decide (Code.width ty = 2)) src idx] ∧
      after = front ∧ src.val = Code.slots C.LOCALS + Code.slots front := by
  generalize equality : instr.GLOBAL_SET (.mk_uN index) = instruction at emission
  cases emission with
  | linear pure => rw [←equality] at pure; exact False.elim (linearEmission_not_globalSet pure)
  | globalSet stack ty idx src lookup position =>
    cases equality
    exact ⟨_,ty,idx,src,rfl,rfl,lookup,rfl,rfl,position⟩
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
end Exec.Interp
