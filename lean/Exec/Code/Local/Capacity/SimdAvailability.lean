import Exec.Code.Local.Capacity.LiteralBudgetAvailability
import Exec.Code.Local.Capacity.AuxiliaryAvailability
import Exec.Code.Local.Capacity.SimdConstructorAvailability
import Exec.Code.Local.Lowering.Simd.SimdOpcodeReduction

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Nonconstant SIMD lowering accepts from independent source meaning and
stack lengths. Temporary arithmetic and the immediate-table request are
bounded explicitly; source meaning discharges constructor coverage. -/
theorem compiler_simd_nonconstant_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub a : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val) (bounded : sub.val < 256)
    (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) input source output)
    (layout : CompilerLayout compiler (front ++ input))
    (postLength : state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableIndex : compiler.function.simd.length ≤ U32.max)
    (tableCapacity : compiler.function.simd.length < Usize.max)
    (tableReserve : compiler.function.simd.length + 1 ≤ bound) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops compiler state opcode a bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have notConstant : opcode ≠ 524#u16 := by
    intro same
    have numeric := congrArg UScalar.val same
    change opcode.val = 524 at numeric
    omega
  rw [compiler_simd_nonconstant_eq ops compiler state opcode a bits notConstant (by omega) (by omega)]
  obtain ⟨reduced,reducedEq,subEq⟩ := simd_opcode_reduction opcode sub number
  unfold simdLowering
  simp only [reducedEq,lift,bind_ok,←subEq,simd_stores_eq,simd_outputs_eq]
  have beforeLength := layout.operands_length
  have outputs := meaning.output_count
  have positive := meaning.input_positive
  simp only [List.length_append] at beforeLength postLength
  have addSpec := Usize.checked_add_bv_spec (alloc.vec.Vec.len compiler.before)
    (if simdStores sub then 0#usize else 1#usize)
  cases added : Usize.checked_add (alloc.vec.Vec.len compiler.before)
      (if simdStores sub then 0#usize else 1#usize) with
  | none =>
    simp only [added] at addSpec
    split at addSpec <;> scalar_tac
  | some total =>
    simp only [added] at addSpec
    have totalCount : total.val = compiler.before.length + (if simdStores sub then 0 else 1) := by
      split at addSpec <;> simp_all only [↓reduceIte] <;> scalar_tac
    simp only [added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have subSpec := Usize.checked_sub_bv_spec total (alloc.vec.Vec.len state.vals)
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none => simp only [subtracted] at subSpec; scalar_tac
    | some consumed =>
      simp only [subtracted] at subSpec
      have consumedCount : consumed.val = input.length := by scalar_tac
      simp only [subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      obtain ⟨status,read,operand,accepted,_⟩ := WP.spec_imp_exists
        (compiler_operand ops compiler _ layout consumed (by omega) (by simp [consumedCount]))
      subst status
      rw [read]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with bounded_index_available (alloc.vec.Vec.len compiler.function.simd) tableIndex
        as ⟨status,index,accepted,_⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,simd_lane_eq]
      step with budget_push_available ops bound available compiler.budget compiler.function.simd
        ({offset := a,lane := simdLane sub a bits,bits} : runtime.bytecode.SimdImmediate) tableCapacity tableReserve
        as ⟨status,budget,values,accepted,same,_⟩
      rw [accepted,same]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      obtain ⟨instruction,constructed⟩ := meaning.constructor_available bounded operand operand index
      rw [constructed]
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      let allocated := {compiler with function := {compiler.function with simd := values}}
      have afterDemand : CallbackDemand allocated state bound :=
        ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,
          demand.sourceReserve,demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
      exact finish_op_available_effect ops bound available allocated state afterDemand instruction

end Itasca.Runtime.Code
