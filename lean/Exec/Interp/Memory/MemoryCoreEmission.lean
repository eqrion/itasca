import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Abs.Numeric.Decode
namespace Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

theorem load_source_injective (left right : Abs.Memory.Load) (a b : memarg)
    (equal : left.source a = right.source b) : left = right ∧ a = b := by
  cases left with
  | full ty =>
    cases right with
    | full other => simp_all [Abs.Memory.Load.source,Abs.Memory.Load.type,Abs.Memory.Load.operation]
    | packed other width sign => simp [Abs.Memory.Load.source,Abs.Memory.Load.type,Abs.Memory.Load.operation] at equal
  | packed ty width sign =>
    cases right with
    | full other => simp [Abs.Memory.Load.source,Abs.Memory.Load.type,Abs.Memory.Load.operation] at equal
    | packed other width' sign' =>
      cases ty <;> cases other <;> cases width <;> cases width' <;> cases sign <;> cases sign' <;>
        simp_all [Abs.Memory.Load.source,Abs.Memory.Load.type,Abs.Memory.Load.operation,Abs.Memory.PackedWidth.size,Abs.Memory.PackedWidth.bits,numtype_Inn]

theorem store_source_injective (left right : Abs.Memory.Store) (a b : memarg)
    (equal : left.source a = right.source b) : left = right ∧ a = b := by
  cases left with
  | full ty =>
    cases right with
    | full other => simp_all [Abs.Memory.Store.source,Abs.Memory.Store.type,Abs.Memory.Store.operation]
    | packed other width => simp [Abs.Memory.Store.source,Abs.Memory.Store.type,Abs.Memory.Store.operation] at equal
  | packed ty width =>
    cases right with
    | full other => simp [Abs.Memory.Store.source,Abs.Memory.Store.type,Abs.Memory.Store.operation] at equal
    | packed other width' =>
      cases ty <;> cases other <;> cases width <;> cases width' <;>
        simp_all [Abs.Memory.Store.source,Abs.Memory.Store.type,Abs.Memory.Store.operation,Abs.Memory.PackedWidth.size,Abs.Memory.PackedWidth.bits,numtype_Inn]

theorem linearEmission_not_load {locals before after emitted ty packed argument}
    (emission : Code.LinearEmission locals before (.LOAD ty packed argument) emitted after) : False := by
  generalize equality : instr.LOAD ty packed argument = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Code.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem linearEmission_not_store {locals before after emitted ty packed argument}
    (emission : Code.LinearEmission locals before (.STORE ty packed argument) emitted after) : False := by
  generalize equality : instr.STORE ty packed argument = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Code.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem scalarEmission_load_inv {C before after emitted} (op : Abs.Memory.Load) (argument : memarg)
    (emission : Code.ScalarEmission C before (op.source argument) emitted after) :
    ∃ stack address offset, before = stack ++ [.I32] ∧
      emitted = [Code.memoryLoadInstruction op address address offset] ∧ after = stack ++ [valtype_numtype op.type] ∧
      argument.OFFSET = .mk_uN offset.val ∧ address.val = Code.slots C.LOCALS + Code.slots stack := by
  generalize equality : op.source argument = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linearEmission_not_load pure)
  | load stack other arg address offset memory available sourceOffset position =>
    obtain ⟨rfl,rfl⟩ := load_source_injective op other argument arg equality
    exact ⟨stack,address,offset,rfl,rfl,rfl,sourceOffset,position⟩
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality

theorem scalarEmission_store_inv {C before after emitted} (op : Abs.Memory.Store) (argument : memarg)
    (emission : Code.ScalarEmission C before (op.source argument) emitted after) :
    ∃ stack address value offset, before = stack ++ [.I32,valtype_numtype op.type] ∧
      emitted = [Code.memoryStoreInstruction op address value offset] ∧ after = stack ∧
      argument.OFFSET = .mk_uN offset.val ∧ address.val = Code.slots C.LOCALS + Code.slots stack ∧ value.val = address.val+1 := by
  generalize equality : op.source argument = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linearEmission_not_store pure)
  | store stack other arg address value offset memory available sourceOffset addressPosition valuePosition =>
    obtain ⟨rfl,rfl⟩ := store_source_injective op other argument arg equality
    exact ⟨_,address,value,offset,rfl,rfl,rfl,sourceOffset,addressPosition,valuePosition⟩
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
end Exec.Interp.MemoryDescriptor
