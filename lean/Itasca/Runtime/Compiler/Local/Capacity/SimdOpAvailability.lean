import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdMeaningCounts
import Mathlib.Tactic.IntervalCases
import Itasca.Runtime.Compiler.Local.Capacity.LiteralBudgetAvailability
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdOpcodeReduction
import Itasca.Runtime.Compiler.Local.Capacity.DeadOpAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch

/-!
Availability of SIMD opcode construction and compiler callbacks. Immediate-meaning certificates discharge constructor obligations before constant/nonconstant replay.
-/

/-! ## Simd Constructor Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

/-- Independent source opcode meaning excludes every reserved constructor
case. This covers all nonconstant SIMD families, without assuming construction
or successful compilation. -/
theorem SimdImmediateMeaning.constructor_available {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (bounded : opcode.val < 256) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  rcases opcode with ⟨⟨number,numberBound⟩⟩
  change number < 256 at bounded
  interval_cases number <;> first
    | exact ⟨_,rfl⟩
    | (cases meaning with
      | pure _ _ _ decoded => change none = some _ at decoded; contradiction
      | lane _ _ _ decoded _ _ => change none = some _ at decoded; contradiction
      | memory _ _ _ decoded _ _ _ _ _ _ => change none = some _ at decoded; contradiction)

end Itasca.Runtime.Code

end

/-! ## Simd Availability -/

section

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

end

/-! ## Simd Op Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual ordinary dispatch for every meaningful nonconstant SIMD opcode
accepts on live and dead paths. The immediate ledger bounds its own reserve. -/
theorem compiler_simd_nonconstant_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512+sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨out,actual,post⟩ := WP.spec_imp_exists
      (compiler_simd_nonconstant_available ops bound available compiler state demand C front input output source
        opcode sub a bits number bounded nonconstant meaning (layout live) (postLength live) operandCapacity
        (tableBound.trans demand.pc) (tableBound.trans_lt demand.codeCapacity)
        ((Nat.add_le_add_right tableBound 1).trans demand.codeReserve))
    exact WP.exists_imp_spec ⟨out,
      (lower_simd_dispatch ops compiler state opcode a b bits live (by omega) (by omega)).trans actual,post⟩
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler state opcode a b bits live
      demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- The actual vector-constant dispatch accepts its bounded pool append and
instruction charge, including dead code where no pool entry is allocated. -/
theorem compiler_simd_constant_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bits : U128)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 524#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨out,actual,post⟩ := WP.spec_imp_exists
      (compiler_vector_literal_available_budget ops bound available compiler state demand poolBound bits)
    obtain ⟨used,budgetEq,usedEq⟩ := post.2
    have effect : CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) := by
      rw [budgetEq]
      exact .of_counter .instructions compiler.budget used 1
        (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)
    exact WP.exists_imp_spec ⟨out,
      (lower_simd_dispatch ops compiler state 524#u16 0#u32 0#u32 bits live (by decide) (by decide)).trans actual,
      post.1,effect⟩
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler state 524#u16 0#u32 0#u32 bits live
      demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code

end
