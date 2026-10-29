import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.SourceMachine.Numeric.Decode
namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

theorem load_source_injective (left right : SourceMachine.Memory.Load) (a b : memarg)
    (equal : left.source a = right.source b) : left = right ∧ a = b := by
  cases left with
  | full ty =>
    cases right with
    | full other => simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Load.type,SourceMachine.Memory.Load.operation]
    | packed other width sign => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Load.type,SourceMachine.Memory.Load.operation] at equal
  | packed ty width sign =>
    cases right with
    | full other => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Load.type,SourceMachine.Memory.Load.operation] at equal
    | packed other width' sign' =>
      cases ty <;> cases other <;> cases width <;> cases width' <;> cases sign <;> cases sign' <;>
        simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Load.type,SourceMachine.Memory.Load.operation,SourceMachine.Memory.PackedWidth.size,SourceMachine.Memory.PackedWidth.bits,numtype_Inn]

theorem store_source_injective (left right : SourceMachine.Memory.Store) (a b : memarg)
    (equal : left.source a = right.source b) : left = right ∧ a = b := by
  cases left with
  | full ty =>
    cases right with
    | full other => simp_all [SourceMachine.Memory.Store.source,SourceMachine.Memory.Store.type,SourceMachine.Memory.Store.operation]
    | packed other width => simp [SourceMachine.Memory.Store.source,SourceMachine.Memory.Store.type,SourceMachine.Memory.Store.operation] at equal
  | packed ty width =>
    cases right with
    | full other => simp [SourceMachine.Memory.Store.source,SourceMachine.Memory.Store.type,SourceMachine.Memory.Store.operation] at equal
    | packed other width' =>
      cases ty <;> cases other <;> cases width <;> cases width' <;>
        simp_all [SourceMachine.Memory.Store.source,SourceMachine.Memory.Store.type,SourceMachine.Memory.Store.operation,SourceMachine.Memory.PackedWidth.size,SourceMachine.Memory.PackedWidth.bits,numtype_Inn]

theorem linear_emission_not_load {locals before after emitted ty packed argument}
    (emission : Compiler.LinearEmission locals before (.LOAD ty packed argument) emitted after) : False := by
  generalize equality : instr.LOAD ty packed argument = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem linear_emission_not_store {locals before after emitted ty packed argument}
    (emission : Compiler.LinearEmission locals before (.STORE ty packed argument) emitted after) : False := by
  generalize equality : instr.STORE ty packed argument = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem scalar_emission_load_inv {C before after emitted} (op : SourceMachine.Memory.Load) (argument : memarg)
    (emission : Compiler.ScalarEmission C before (op.source argument) emitted after) :
    ∃ stack address offset, before = stack ++ [.I32] ∧
      emitted = [Compiler.memoryLoadInstruction op address address offset] ∧ after = stack ++ [valtype_numtype op.type] ∧
      argument.OFFSET = .mk_uN offset.val ∧ address.val = Compiler.slots C.LOCALS + Compiler.slots stack := by
  generalize equality : op.source argument = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linear_emission_not_load pure)
  | load stack other arg address offset memory available sourceOffset position =>
    obtain ⟨rfl,rfl⟩ := load_source_injective op other argument arg equality
    exact ⟨stack,address,offset,rfl,rfl,rfl,sourceOffset,position⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality

theorem scalar_emission_store_inv {C before after emitted} (op : SourceMachine.Memory.Store) (argument : memarg)
    (emission : Compiler.ScalarEmission C before (op.source argument) emitted after) :
    ∃ stack address value offset, before = stack ++ [.I32,valtype_numtype op.type] ∧
      emitted = [Compiler.memoryStoreInstruction op address value offset] ∧ after = stack ∧
      argument.OFFSET = .mk_uN offset.val ∧ address.val = Compiler.slots C.LOCALS + Compiler.slots stack ∧ value.val = address.val+1 := by
  generalize equality : op.source argument = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linear_emission_not_store pure)
  | store stack other arg address value offset memory available sourceOffset addressPosition valuePosition =>
    obtain ⟨rfl,rfl⟩ := store_source_injective op other argument arg equality
    exact ⟨_,address,value,offset,rfl,rfl,rfl,sourceOffset,addressPosition,valuePosition⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
end Itasca.Runtime.Interp.MemoryDescriptor
