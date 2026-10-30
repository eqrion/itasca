import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Lowering
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission

/-!
Scalar memory lowering, operands and emitted instruction relations. Opcode descriptors and numeric safety remain independently consumed.
-/

/-! ## Memory Lowering -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable def memoryLoadLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Memory.Load) (offset : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let r ←
    runtime.compiler.FunctionCompiler.operand ops compiler
      1#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let o ← runtime.bytecode.Instr.make_load (memoryLoadOpcode op) val val1 offset
      let r1 ←
        core.option.Option.ok_or o
          _root_.Itasca.error.VisitError.OutOfMemory
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          compiler state val2
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r2, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r1, compiler)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    ok (r1, compiler)

theorem lower_memory_load_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Memory.Load) (offset alignment : U32) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128 =
      memoryLoadLowering ops compiler state op offset := by
  cases op with
  | full ty => cases ty <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl
  | packed ty width sign =>
    cases ty <;> cases width <;> cases sign <;>
      unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl

noncomputable def memoryStoreLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Memory.Store) (offset : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let r ←
    runtime.compiler.FunctionCompiler.operand ops compiler
      2#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        1#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let o ← runtime.bytecode.Instr.make_store (memoryStoreOpcode op) val val1 offset
      let r2 ←
        core.option.Option.ok_or o
          _root_.Itasca.error.VisitError.OutOfMemory
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          compiler state val2
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r3, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r2, compiler)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    ok (r1, compiler)

theorem lower_memory_store_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Memory.Store) (offset alignment : U32) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128 =
      memoryStoreLowering ops compiler state op offset := by
  cases op with
  | full ty => cases ty <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl
  | packed ty width =>
    cases ty <;> cases width <;>
      unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl

theorem lower_memory_load_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Memory.Load) (offset alignment address : U32) (reachable : compiler.reachable = true)
    (operand : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok address)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (memoryLoadInstruction op address address offset) := by
  rw [lower_memory_load_dispatch ops compiler state op offset alignment reachable]
  unfold memoryLoadLowering
  simp only [operand, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    memory_load_instruction_make, core.option.Option.ok_or]

theorem lower_memory_store_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : SourceMachine.Memory.Store) (offset alignment address value : U32) (reachable : compiler.reachable = true)
    (addressOperand : runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok address))
    (valueOperand : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok value)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (memoryStoreInstruction op address value offset) := by
  rw [lower_memory_store_dispatch ops compiler state op offset alignment reachable]
  unfold memoryStoreLowering
  simp only [addressOperand, valueOperand, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    memory_store_instruction_make, core.option.Option.ok_or]
end Itasca.Runtime.Compiler

end

/-! ## Memory Operands -/

section

namespace Itasca.Runtime.Compiler
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
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (front : List valtype) (op : SourceMachine.Memory.Load) (offset alignment : U32)
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
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (front : List valtype) (op : SourceMachine.Memory.Store) (offset alignment : U32)
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
end Itasca.Runtime.Compiler

end

/-! ## Memory Emission -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_memory_load_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (front : List valtype) (op : SourceMachine.Memory.Load) (offset alignment : U32)
    (C : context) (memory : memtype) (argument : memarg)
    (locals : C.LOCALS = compilerLocals compiler) (available : C.MEMS[0]? = some memory)
    (sourceOffset : argument.OFFSET = .mk_uN offset.val)
    (layout : CompilerLayout compiler (front ++ [.I32])) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [valtype_numtype op.type])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () → ∃ instruction,
        Lowered compiler out.2 instruction (front ++ [valtype_numtype op.type]) ∧
        ScalarEmission C (front ++ [.I32]) (op.source argument) [instruction] (front ++ [valtype_numtype op.type]) ⦄ := by
  apply WP.spec_mono (compiler_memory_load_lowered ops law compiler state types front op offset alignment
    layout reachable concrete typed codeFits sourceFits coordinateFits)
  intro out success accepted
  obtain ⟨address,position,lowered⟩ := success accepted
  exact ⟨_,lowered,.load front op argument address offset memory available sourceOffset (by simpa only [locals] using position)⟩

@[step] theorem compiler_memory_store_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (front : List valtype) (op : SourceMachine.Memory.Store) (offset alignment : U32)
    (C : context) (memory : memtype) (argument : memarg)
    (locals : C.LOCALS = compilerLocals compiler) (available : C.MEMS[0]? = some memory)
    (sourceOffset : argument.OFFSET = .mk_uN offset.val)
    (layout : CompilerLayout compiler (front ++ [.I32,valtype_numtype op.type])) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () → ∃ instruction,
        Lowered compiler out.2 instruction front ∧
        ScalarEmission C (front ++ [.I32,valtype_numtype op.type]) (op.source argument) [instruction] front ⦄ := by
  apply WP.spec_mono (compiler_memory_store_lowered ops law compiler state types front op offset alignment
    layout reachable concrete typed codeFits sourceFits coordinateFits)
  intro out success accepted
  obtain ⟨address,value,addressPosition,valuePosition,lowered⟩ := success accepted
  exact ⟨_,lowered,.store front op argument address value offset memory available sourceOffset
    (by simpa only [locals] using addressPosition) valuePosition⟩
end Itasca.Runtime.Compiler

end
