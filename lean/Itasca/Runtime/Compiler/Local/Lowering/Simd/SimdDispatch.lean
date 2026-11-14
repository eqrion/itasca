import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSuccess
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Binary.Wasm2.SyntaxUnique

/-!
Sections, each formerly its own module: SimdLowering, SimdEmission, SimdMeaningCounts, SimdLoweringSuccess, SimdOpcodeReduction, SimdLowered, SimdDispatch.
-/

/-! ## SimdLowering -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts
end Itasca.Runtime.Compiler
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

end Itasca.Runtime.Compiler

end

/-! ## SimdEmission -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca.Wasm2.Simd

/-- Source syntax and immediate fields retained by a SIMD metadata entry.
The opcode meanings are the independent binary-decoding tables. -/
inductive SimdImmediateMeaning (C : context) : U32 → runtime.bytecode.SimdImmediate →
    List valtype → instr → List valtype → Prop where
  | pure (opcode : U32) (immediate : runtime.bytecode.SimdImmediate) (op : Operation)
      (meaning : pureMeaning opcode.val = some op) :
      SimdImmediateMeaning C opcode immediate op.signature.inputs op.instruction op.signature.outputs
  | lane (opcode : U32) (immediate : runtime.bytecode.SimdImmediate) (op : LaneOperation)
      (meaning : laneMeaning opcode.val = some op) (lane : U8)
      (position : immediate.lane.val = lane.val) :
      SimdImmediateMeaning C opcode immediate op.inputs (op.instruction (.mk_uN lane.val)) op.outputs
  | memory (opcode : U32) (immediate : runtime.bytecode.SimdImmediate) (op : MemoryOperation)
      (meaning : memoryMeaning opcode.val = some op) (argument : memarg) (lane : U8)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (offset : argument.OFFSET = .mk_uN immediate.offset.val)
      (position : op.laneCount ≠ 0 → immediate.lane.val = lane.val) :
      SimdImmediateMeaning C opcode immediate op.inputs (op.instruction argument (.mk_uN lane.val)) op.outputs
  | shuffle (immediate : runtime.bytecode.SimdImmediate) (low high : U64)
      (bits : immediate.bits.val = low.val + high.val * 2^64) :
      SimdImmediateMeaning C 13#u32 immediate [.V128,.V128] (shuffle low high) [.V128]

/-- Exact SIMD instruction, slot, and function-local metadata correspondence.
Execution correctness and source typing are established separately. -/
inductive SimdEmission (immediates : List runtime.bytecode.SimdImmediate) (constants : List U128)
    (C : context) : List valtype → instr → List Bytecode → List valtype → Prop where
  | instruction (front input output : List valtype) (source : instr)
      (opcode operand entry : U32) (immediate : runtime.bytecode.SimdImmediate) (instruction : Bytecode)
      (meaning : SimdImmediateMeaning C opcode immediate input source output)
      (metadata : immediates[entry.val]? = some immediate)
      (constructed : runtime.bytecode.Instr.make_simd opcode operand operand entry = .ok (some instruction))
      (position : operand.val = slots C.LOCALS + slots front) :
      SimdEmission immediates constants C (front ++ input) source [instruction] (front ++ output)
  | constant (front : List valtype) (bits : U128) (dst entry : U32)
      (metadata : constants[entry.val]? = some bits)
      (position : dst.val = slots C.LOCALS + slots front) :
      SimdEmission immediates constants C front (.VCONST .V128 (.mk_uN bits.val))
        [.ConstV128 dst entry] (front ++ [.V128])

theorem SimdEmission.length_one {immediates constants C before source code after}
    (emission : SimdEmission immediates constants C before source code after) : code.length = 1 := by
  cases emission <;> rfl

theorem SimdEmission.append_tables {immediates constants C before source code after}
    (emission : SimdEmission immediates constants C before source code after)
    (extraImmediates : List runtime.bytecode.SimdImmediate) (extraConstants : List U128) :
    SimdEmission (immediates ++ extraImmediates) (constants ++ extraConstants) C before source code after := by
  cases emission with
  | instruction front input output source opcode operand entry immediate instruction meaning metadata constructed position =>
    apply SimdEmission.instruction front input output source opcode operand entry immediate instruction meaning _ constructed position
    have bound := (List.getElem?_eq_some_iff.mp metadata).1
    simpa [List.getElem?_append,bound] using metadata
  | constant front bits dst entry metadata position =>
    apply SimdEmission.constant _ bits dst entry _ position
    have bound := (List.getElem?_eq_some_iff.mp metadata).1
    simpa [List.getElem?_append,bound] using metadata

theorem SimdImmediateMeaning.context {C D opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (memories : C.MEMS = D.MEMS) :
    SimdImmediateMeaning D opcode immediate input source output := by
  cases meaning with
  | pure opcode immediate op meaning => exact .pure opcode immediate op meaning
  | lane opcode immediate op meaning lane position => exact .lane opcode immediate op meaning lane position
  | memory opcode immediate op meaning argument lane memory available offset position =>
    exact .memory opcode immediate op meaning argument lane memory (memories ▸ available) offset position
  | shuffle immediate low high bits => exact .shuffle immediate low high bits

theorem SimdEmission.context {immediates constants C D before source code after}
    (emission : SimdEmission immediates constants C before source code after)
    (memories : C.MEMS = D.MEMS) (locals : C.LOCALS = D.LOCALS) :
    SimdEmission immediates constants D before source code after := by
  cases emission with
  | instruction front input output source opcode operand entry immediate instruction meaning metadata constructed position =>
    exact .instruction front input output source opcode operand entry immediate instruction
      (meaning.context memories) metadata constructed (locals ▸ position)
  | constant front bits dst entry metadata position =>
    exact .constant _ bits dst entry metadata (locals ▸ position)

end Itasca.Runtime.Compiler

end

/-! ## SimdMeaningCounts -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
theorem SimdImmediateMeaning.input_positive {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) : 0 < input.length := by
  cases meaning with
  | pure opcode immediate op meaning => cases op.signature <;> decide
  | lane opcode immediate op meaning lane position => cases op <;> decide
  | memory opcode immediate op meaning argument lane memory available offset position => cases op <;> decide
  | shuffle => decide

private theorem not_store_of_pure (opcode : U32) (op : Operation)
    (meaning : pureMeaning opcode.val = some op) : simdStores opcode = false := by
  unfold simdStores
  split
  · rename_i eleven
    have number : opcode.val = 11 := by simpa using congrArg UScalar.val eleven
    rw [number] at meaning
    change none = some op at meaning
    contradiction
  · split
    · rename_i lower
      have notUpper : ¬ opcode ≤ 91#u32 := by
        intro upper
        have low : 88 ≤ opcode.val := by scalar_tac
        have high : opcode.val ≤ 91 := by scalar_tac
        have cases : opcode.val = 88 ∨ opcode.val = 89 ∨ opcode.val = 90 ∨ opcode.val = 91 := by omega
        rcases cases with h | h | h | h
        all_goals rw [h] at meaning
        all_goals change none = some op at meaning
        all_goals contradiction
      simp [notUpper]
    · rfl

private theorem not_store_of_lane (opcode : U32) (op : LaneOperation)
    (meaning : laneMeaning opcode.val = some op) : simdStores opcode = false := by
  unfold simdStores
  split
  · rename_i eleven
    have number : opcode.val = 11 := by simpa using congrArg UScalar.val eleven
    rw [number] at meaning
    change none = some op at meaning
    contradiction
  · split
    · rename_i lower
      have notUpper : ¬ opcode ≤ 91#u32 := by
        intro upper
        have low : 88 ≤ opcode.val := by scalar_tac
        have high : opcode.val ≤ 91 := by scalar_tac
        have cases : opcode.val = 88 ∨ opcode.val = 89 ∨ opcode.val = 90 ∨ opcode.val = 91 := by omega
        rcases cases with h | h | h | h
        all_goals rw [h] at meaning
        all_goals change none = some op at meaning
        all_goals contradiction
      simp [notUpper]
    · rfl

private theorem store_of_memory (opcode : U32) (op : MemoryOperation)
    (meaning : memoryMeaning opcode.val = some op) : simdStores opcode = op.store := by
  unfold memoryMeaning at meaning
  split at meaning
  all_goals simp only [Option.some.injEq, reduceCtorEq] at meaning
  all_goals first | contradiction | subst op
  all_goals simp only [simdStores,MemoryOperation.store]
  all_goals split_ifs <;> scalar_tac

theorem SimdImmediateMeaning.output_count {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) :
    output.length = if simdStores opcode then 0 else 1 := by
  cases meaning with
  | pure opcode immediate op meaning =>
    rw [not_store_of_pure opcode op meaning]
    cases op.signature <;> rfl
  | lane opcode immediate op meaning lane position =>
    rw [not_store_of_lane opcode op meaning]
    cases op <;> rfl
  | memory opcode immediate op meaning argument lane memory available offset position =>
    rw [store_of_memory opcode op meaning]
    cases op <;> rfl
  | shuffle => rfl
end Itasca.Runtime.Compiler

end

/-! ## SimdLoweringSuccess -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

theorem simd_lowering_allocation_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode reduced : U16) (sub a operand : U32) (bits : U128) (totalCount operandCount : Usize)
    (reducedEq : (opcode - 512#u16) = Result.ok reduced)
    (subEq : sub = UScalar.cast .U32 reduced)
    (added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores sub then 0#usize else 1#usize) = some totalCount)
    (subtracted : Usize.checked_sub totalCount (alloc.vec.Vec.len state.vals) = some operandCount)
    (operandEq : runtime.compiler.FunctionCompiler.operand ops before operandCount = .ok (.Ok operand))
    (accepted : simdLowering ops before state opcode a bits = .ok (.Ok (),after)) :
    ∃ entry budget immediates instruction,
      runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.simd) = .ok (.Ok entry) ∧
      runtime.compiler.Budget.push ops before.budget before.function.simd (simdImmediate sub a bits) = .ok (.Ok (),budget,immediates) ∧
      runtime.bytecode.Instr.make_simd sub operand operand entry = .ok (some instruction) ∧
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        {before with budget,function := {before.function with simd := immediates}} state instruction = .ok (.Ok (),after) := by
  have effect := (simdLowering.inv ops before after state opcode a bits (.Ok ()) accepted).at_reduced reducedEq
  rw [← subEq] at effect
  unfold SimdOperandEffect at effect
  simp only [added, subtracted] at effect
  obtain ⟨answer, read, allocated⟩ := effect
  rw [operandEq] at read
  have same : answer = .Ok operand := (Result.ok_injective read).symm
  subst answer
  exact allocated.success

end Itasca.Runtime.Compiler
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

end Itasca.Runtime.Compiler

end

/-! ## SimdOpcodeReduction -/

section

/-!
SIMD lowering operand counts and opcode reduction. Count-position facts discharge the arithmetic side conditions of the reduction theorem.
-/

/-! ## Simd Operand Counts -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts
theorem simd_lowering_operand_counts {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode reduced : U16) (sub a : U32) (bits : U128)
    (reducedEq : (opcode - 512#u16) = Result.ok reduced)
    (subEq : sub = UScalar.cast .U32 reduced)
    (accepted : simdLowering ops before state opcode a bits = .ok (.Ok (),after)) :
    ∃ totalCount operandCount operand,
      Usize.checked_add (alloc.vec.Vec.len before.before)
        (if simdStores sub then 0#usize else 1#usize) = some totalCount ∧
      Usize.checked_sub totalCount (alloc.vec.Vec.len state.vals) = some operandCount ∧
      runtime.compiler.FunctionCompiler.operand ops before operandCount = .ok (.Ok operand) := by
  have effect := (simdLowering.inv ops before after state opcode a bits (.Ok ()) accepted).at_reduced reducedEq
  rw [← subEq] at effect
  obtain ⟨total, consumed, source, added, subtracted, operand, _⟩ := effect.success
  exact ⟨total, consumed, source, added, subtracted, operand⟩

theorem simd_count_position {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (front input output : List valtype) (sub operand : U32) (totalCount operandCount : Usize)
    (layout : CompilerLayout before (front ++ input))
    (postLength : state.vals.val.length = (front ++ output).length)
    (outputCount : output.length = if simdStores sub then 0 else 1)
    (positive : 0 < input.length)
    (added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores sub then 0#usize else 1#usize) = some totalCount)
    (subtracted : Usize.checked_sub totalCount (alloc.vec.Vec.len state.vals) = some operandCount)
    (read : runtime.compiler.FunctionCompiler.operand ops before operandCount = .ok (.Ok operand)) :
    operandCount.val = input.length ∧ operand.val = slots (compilerLocals before) + slots front := by
  have beforeLength := layout.operands_length
  have addSpec := Usize.checked_add_bv_spec (alloc.vec.Vec.len before.before)
    (if simdStores sub then 0#usize else 1#usize)
  have subSpec := Usize.checked_sub_bv_spec totalCount (alloc.vec.Vec.len state.vals)
  simp only [added] at addSpec
  simp only [subtracted] at subSpec
  have count : operandCount.val = input.length := by
    simp only [List.length_append] at beforeLength postLength
    split at outputCount
    · rename_i store
      simp only [store,↓reduceIte] at addSpec
      scalar_tac
    · rename_i store
      simp only [store,↓reduceIte] at addSpec
      scalar_tac
  obtain ⟨r,executed,first,rfl,position⟩ := WP.spec_imp_exists
    (compiler_operand ops before _ layout operandCount (by omega) (by simp [count]))
  have same : first = operand := by simpa only [read,Result.ok.injEq,core.result.Result.Ok.injEq] using executed.symm
  subst first
  exact ⟨count,by simpa [offset,List.length_append,count] using position⟩
end Itasca.Runtime.Compiler

end

/-! ## Simd Opcode Reduction -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem simd_opcode_reduction (opcode : U16) (sub : U32)
    (number : opcode.val = 512 + sub.val) :
    ∃ reduced : U16, (opcode - 512#u16) = Result.ok reduced ∧ sub = UScalar.cast .U32 reduced := by
  obtain ⟨reduced,subtracted,value⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := opcode) (y := 512#u16) (by scalar_tac))
  refine ⟨reduced,subtracted,?_⟩
  apply UScalar.eq_of_val_eq
  have bound := reduced.hBounds
  rw [UScalar.cast_val_eq]
  scalar_tac
end Itasca.Runtime.Compiler

end

end

/-! ## SimdLowered -/

section

/-!
SIMD lowering certificates through constant emission and final table metadata. The final emission results retain both instruction bytes and compiler table relationships.
-/

/-! ## Simd Const Lowering -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

theorem simd_const_lowering_allocation_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state 524#u16 a bits = .ok (.Ok (),after)) :
    ∃ entry budget values,
      runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.v128_pool) = .ok (.Ok entry) ∧
      runtime.compiler.Budget.push ops before.budget before.function.v128_pool bits = .ok (.Ok (),budget,values) ∧
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        {before with budget,function := {before.function with v128_pool := values}} state
        (.ConstV128 before.height entry) = .ok (.Ok (),after) := by
  exact (simd_constant_inv ops before after state a bits (.Ok ()) accepted).success

end Itasca.Runtime.Compiler

end

/-! ## Simd Finish Tables -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem compiler_finish_simd_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (),after)) :
    after.function.simd = before.function.simd ∧ after.function.v128_pool = before.function.v128_pool := by
  obtain ⟨middle, emitted, rest⟩ :=
    (runtime.compiler.lower.FunctionCompiler.finish_op.inv ops before after state instruction (.Ok ()) accepted).success
  have frame := compiler_observe_frame ops law middle state
  rw [rest,WP.spec_ok] at frame
  change ObserveFrame middle after at frame
  obtain ⟨budget,code,sources,middleEq,_,_⟩ := compiler_emit_success ops law before middle instruction emitted
  rw [frame,middleEq]
  exact ⟨rfl,rfl⟩
end Itasca.Runtime.Compiler

end

/-! ## Simd Lowered -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
/-- Accepted SIMD compilation derives the exact instruction, table append and
post-layout from the validated source signature and actual compiler state. -/
theorem compiler_simd_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (C : context) (front input output : List valtype) (source : instr)
    (opcode : U16) (sub a : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) input source output)
    (locals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before (front ++ input))
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ output)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    after.function.simd.val = before.function.simd.val ++ [simdImmediate sub a bits] ∧
    after.function.v128_pool = before.function.v128_pool ∧ ∃ instruction,
      Lowered before after instruction (front ++ output) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ input) source [instruction] (front ++ output) := by
  have notConstant : opcode ≠ 524#u16 := by
    intro equal
    have numberEq := congrArg UScalar.val equal
    change opcode.val = 524 at numberEq
    omega
  rw [compiler_simd_nonconstant_eq ops before state opcode a bits notConstant (by omega) (by omega)] at accepted
  obtain ⟨reduced,reducedEq,subEq⟩ := simd_opcode_reduction opcode sub number
  obtain ⟨totalCount,operandCount,operand,added,subtracted,read⟩ :=
    simd_lowering_operand_counts ops before after state opcode reduced sub a bits reducedEq subEq accepted
  have postLength : state.vals.val.length = (front ++ output).length := by
    rw [concrete,List.length_map,←typed,List.length_map]
  obtain ⟨count,position⟩ := simd_count_position ops before state front input output sub operand totalCount operandCount
    layout postLength meaning.output_count meaning.input_positive added subtracted read
  obtain ⟨entry,budget,immediates,instruction,indexEq,pushed,constructed,finished⟩ :=
    simd_lowering_allocation_success ops before after state opcode reduced sub a operand bits totalCount operandCount
      reducedEq subEq added subtracted read accepted
  let allocated := {before with budget, function := {before.function with simd := immediates}}
  have allocatedLayout : CompilerLayout allocated (front ++ input) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  have lowered := finish_op ops law allocated state types instruction _ allocatedLayout concrete
    codeFits sourceFits coordinateFits
  rw [finished,WP.spec_ok] at lowered
  have kept := compiler_finish_simd_tables ops law allocated after state instruction finished
  have appended := (budget_push_success ops law before.budget budget before.function.simd immediates
    (simdImmediate sub a bits) pushed).2
  have afterTable : after.function.simd.val = before.function.simd.val ++ [simdImmediate sub a bits] := by
    rw [kept.1]; exact appended
  have index := bounded_index (alloc.vec.Vec.len before.function.simd)
  rw [indexEq,WP.spec_ok] at index
  have indexVal : entry.val = before.function.simd.val.length := by simpa using index entry rfl
  refine ⟨afterTable,kept.2,instruction,?_,?_⟩
  · simpa only [typed,Lowered,allocated,compilerLocals] using lowered rfl
  · apply SimdEmission.instruction front input output source sub operand entry (simdImmediate sub a bits)
      instruction meaning _ constructed (by simpa only [locals] using position)
    rw [afterTable,indexVal]
    simp

/-- Vector constants retain exactly their 128 source bits in the allocated
constant-pool entry and use the current validated stack height. -/
theorem compiler_simd_const_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (C : context) (front : List valtype) (a : U32) (bits : U128)
    (locals : C.LOCALS = compilerLocals before) (layout : CompilerLayout before front)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [.V128])
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state 524#u16 a bits = .ok (.Ok (),after)) :
    after.function.v128_pool.val = before.function.v128_pool.val ++ [bits] ∧
    after.function.simd = before.function.simd ∧ ∃ instruction,
      Lowered before after instruction (front ++ [.V128]) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        front (.VCONST .V128 (.mk_uN bits.val)) [instruction] (front ++ [.V128]) := by
  obtain ⟨entry,budget,values,indexEq,pushed,finished⟩ :=
    simd_const_lowering_allocation_success ops before after state a bits accepted
  let allocated := {before with budget, function := {before.function with v128_pool := values}}
  have allocatedLayout : CompilerLayout allocated front :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  have lowered := finish_op ops law allocated state types (.ConstV128 before.height entry) _ allocatedLayout concrete
    codeFits sourceFits coordinateFits
  rw [finished,WP.spec_ok] at lowered
  have kept := compiler_finish_simd_tables ops law allocated after state (.ConstV128 before.height entry) finished
  have appended := (budget_push_success ops law before.budget budget before.function.v128_pool values bits pushed).2
  have afterTable : after.function.v128_pool.val = before.function.v128_pool.val ++ [bits] := by
    rw [kept.2]; exact appended
  have index := bounded_index (alloc.vec.Vec.len before.function.v128_pool)
  rw [indexEq,WP.spec_ok] at index
  have indexVal : entry.val = before.function.v128_pool.val.length := by simpa using index entry rfl
  refine ⟨afterTable,kept.1,.ConstV128 before.height entry,?_,?_⟩
  · simpa only [typed,Lowered,allocated,compilerLocals] using lowered rfl
  · apply SimdEmission.constant front bits before.height entry _ (by simpa only [locals] using layout.height)
    rw [afterTable,indexVal]
    simp
end Itasca.Runtime.Compiler

end

end

/-! ## SimdDispatch -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The checked 0xfd compiler opcode interval delegates to SIMD lowering. -/
theorem lower_simd_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a b : U32) (bits : U128)
    (reachable : before.reachable = true) (lower : 512 ≤ opcode.val) (upper : opcode.val < 768) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits =
      runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits := by
  exact runtime.compiler.lower.FunctionCompiler.op.simd ops before state opcode a b bits reachable ⟨lower, by omega⟩

end Itasca.Runtime.Compiler

end
