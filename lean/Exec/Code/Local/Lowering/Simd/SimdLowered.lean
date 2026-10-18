import Exec.Code.Local.Lowering.Simd.SimdMeaningCounts
import Exec.Code.Local.Lowering.Simd.SimdFinishTables
import Exec.Code.Local.Lowering.Simd.SimdOpcodeReduction
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Accepted SIMD compilation derives the exact instruction, table append and
post-layout from the validated source signature and actual compiler state. -/
theorem compiler_simd_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
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
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
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
end Exec.Code
