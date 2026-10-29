import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.SourceMachine.Numeric.Decode
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem linear_emission_not_global_get {locals before after emitted index}
    (emission : Compiler.LinearEmission locals before (.GLOBAL_GET index) emitted after) : False := by
  generalize equality : instr.GLOBAL_GET index = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem linear_emission_not_global_set {locals before after emitted index}
    (emission : Compiler.LinearEmission locals before (.GLOBAL_SET index) emitted after) : False := by
  generalize equality : instr.GLOBAL_SET index = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem scalar_emission_global_get_inv {C before after emitted} (index : Nat)
    (emission : Compiler.ScalarEmission C before (.GLOBAL_GET (.mk_uN index)) emitted after) :
    ∃ mutability ty idx dst, index = idx.val ∧
      C.GLOBALS[index]? = some (.mk_globaltype mutability ty) ∧
      emitted = [Compiler.globalGetInstruction (decide (Compiler.width ty = 2)) dst idx] ∧
      after = before ++ [ty] ∧ dst.val = Compiler.slots C.LOCALS + Compiler.slots before := by
  generalize equality : instr.GLOBAL_GET (.mk_uN index) = instruction at emission
  cases emission with
  | linear pure => rw [←equality] at pure; exact False.elim (linear_emission_not_global_get pure)
  | globalGet stack mutability ty idx dst lookup position =>
    cases equality
    exact ⟨mutability,ty,idx,dst,rfl,lookup,rfl,rfl,position⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality

theorem scalar_emission_global_set_inv {C before after emitted} (index : Nat)
    (emission : Compiler.ScalarEmission C before (.GLOBAL_SET (.mk_uN index)) emitted after) :
    ∃ front ty idx src, index = idx.val ∧ before = front ++ [ty] ∧
      C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) ∧
      emitted = [Compiler.globalSetInstruction (decide (Compiler.width ty = 2)) src idx] ∧
      after = front ∧ src.val = Compiler.slots C.LOCALS + Compiler.slots front := by
  generalize equality : instr.GLOBAL_SET (.mk_uN index) = instruction at emission
  cases emission with
  | linear pure => rw [←equality] at pure; exact False.elim (linear_emission_not_global_set pure)
  | globalSet stack ty idx src lookup position =>
    cases equality
    exact ⟨_,ty,idx,src,rfl,rfl,lookup,rfl,rfl,position⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
end Itasca.Runtime.Interp
