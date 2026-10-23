import Exec.Code.Local.Relations.Memory.MemoryLowering
import Exec.Code.Local.Lowering.Local.LoweringLocal
import Exec.Code.Local.Relations.Common.ScalarEmission

namespace Exec.Code
open Aeneas Aeneas.Std

/-- A load consumes the final scalar address slot and overwrites that slot. -/
theorem memory_load_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype)
    (layout : CompilerLayout compiler (front ++ [.I32])) :
    ∃ address : U32, runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok address) ∧
      address.val = slots (compilerLocals compiler) + slots front :=
  last_operand ops compiler front .I32 layout

/-- A store consumes an i32 address followed by one scalar numeric value. Both
operands have one-word widths, including f64 and i64. -/
theorem memory_store_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype) (ty : numtype)
    (layout : CompilerLayout compiler (front ++ [.I32,valtype_numtype ty])) :
    ∃ address value : U32,
      runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok address) ∧
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok value) ∧
      address.val = slots (compilerLocals compiler) + slots front ∧ value.val = address.val + 1 := by
  obtain ⟨r,readAddress,address,rfl,addressPosition⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 2#usize (by decide) (by simp))
  obtain ⟨r,readValue,value,rfl,valuePosition⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 1#usize (by decide) (by simp))
  have addressSlot : address.val = slots (compilerLocals compiler) + slots front := by
    simpa [offset,List.take_append] using addressPosition
  have valueSlot : value.val = address.val + 1 := by
    have take : front.take (front.length+1) = front := List.take_of_length_le (by omega)
    rw [addressSlot]
    simpa [offset,List.take_append,slots_append,slots,width,take,Nat.add_assoc] using valuePosition
  exact ⟨address,value,readAddress,readValue,addressSlot,valueSlot⟩

@[step] theorem compiler_memory_load_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (op : Abs.Memory.Load) (offset alignment : U32)
    (layout : CompilerLayout compiler (front ++ [.I32])) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [valtype_numtype op.type])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () → ∃ address : U32,
        address.val = slots (compilerLocals compiler) + slots front ∧
        Lowered compiler out.2 (memoryLoadInstruction op address address offset) (front ++ [valtype_numtype op.type]) ⦄ := by
  obtain ⟨address,read,position⟩ := memory_load_operand ops compiler front layout
  rw [lower_memory_load_eq ops compiler state op offset alignment address reachable read]
  step with finish_op ops law compiler state types (memoryLoadInstruction op address address offset) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out,lowered,success⟩
  exact ⟨address,position,by simpa only [typed] using lowered success⟩

@[step] theorem compiler_memory_store_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (op : Abs.Memory.Store) (offset alignment : U32)
    (layout : CompilerLayout compiler (front ++ [.I32,valtype_numtype op.type])) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () → ∃ address value : U32,
        address.val = slots (compilerLocals compiler) + slots front ∧ value.val = address.val + 1 ∧
        Lowered compiler out.2 (memoryStoreInstruction op address value offset) front ⦄ := by
  obtain ⟨address,value,addressRead,valueRead,addressPosition,valuePosition⟩ := memory_store_operands ops compiler front op.type layout
  rw [lower_memory_store_eq ops compiler state op offset alignment address value reachable addressRead valueRead]
  step with finish_op ops law compiler state types (memoryStoreInstruction op address value offset) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out,lowered,success⟩
  exact ⟨address,value,addressPosition,valuePosition,by simpa only [typed] using lowered success⟩
end Exec.Code
