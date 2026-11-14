import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering

/-!
Sections, each formerly its own module: FunctionStartAvailability, SlotAvailability, BranchTableCapacity, GlobalCapacity.
-/

/-! ## FunctionStartAvailability -/

section

/-!
Availability of function start, from a single local allocation through the local-declaration loop. FunctionStartDemand records the bounds consumed by the entry construction.
-/

/-! ## Function Start Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual function-start callback accepts under independent signature,
coordinate, and resource bounds. It changes precisely the local and root-control
budget counters, preserving every other budget field. -/
theorem compiler_function_start_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context)
    (typeIndex : U32) (signature : runtime.compiler.Signature) (bodyBegin bodyEnd : Usize)
    (lookup : compiler.signatures.val[typeIndex.val]? = some signature)
    (beginFits : compiler.batch_start.val+bodyBegin.val ≤ Usize.max)
    (endFits : compiler.batch_start.val+bodyEnd.val ≤ Usize.max)
    (demand : FunctionStartDemand compiler ctx bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops compiler ctx typeIndex bodyBegin bodyEnd ⦃ out =>
        out.1 = .Ok () ∧ ∃ usedLocals usedControls,
          out.2.budget = {compiler.budget with locals := usedLocals,controls := usedControls} ∧
          usedLocals.val = compiler.budget.locals.val+ctx.locals.val.length ∧
          usedControls.val = compiler.budget.controls.val+1 ⦄ := by
  exact runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.available
    ops bound available compiler ctx typeIndex signature bodyBegin bodyEnd lookup beginFits endFits demand

end Itasca.Runtime.Compiler

end

end

/-! ## SlotAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The executable slot-range gate accepts an independent arithmetic bound. -/
theorem slot_availability_fit_accepts (function : runtime.bytecode.CompiledFunction) (start count : U32)
    (bounded : start.val + count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function start count = .ok true := by
  have lower : start ≤ function.slot_count := by scalar_tac
  have accepts : runtime.bytecode.CompiledFunction.slots_fit function start count ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    rw [if_pos lower]
    step as ⟨remaining,difference⟩
    have fits : count ≤ remaining := by scalar_tac
    simp [fits]
  obtain ⟨result,actual,rfl⟩ := WP.spec_imp_exists accepts
  exact actual

/-- Initializer instructions remain accepted in a larger final slot capacity,
as needed when composing active segment programs. -/
theorem initial_instruction_capacity_accepts (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (instruction : runtime.bytecode.Instr)
    (lowered : InitialInstruction function expr ty instruction)
    (capacity : (initializerWidth ty).val ≤ function.slot_count.val)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  have scalar : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 1#u32 = .ok true := by
    apply slot_availability_fit_accepts
    have positive : 1 ≤ (initializerWidth ty).val := by cases ty <;> decide
    scalar_tac
  have wide (same : ty = .V128) :
      runtime.bytecode.CompiledFunction.slots_fit function 0#u32 2#u32 = .ok true := by
    apply slot_availability_fit_accepts
    simpa [same,initializerWidth] using capacity
  cases lowered <;>
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
      runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
  all_goals first | exact scalar | exact wide rfl | skip
  rename_i lo hi pool embedded
  rw [wide (vector lo hi rfl),bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp embedded).1
  simpa [lift] using inside

end Itasca.Runtime.Compiler

end

/-! ## BranchTableCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem compiler_table_branch_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]?=some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index=.ok (.Ok (),after)) :
    capacityMetadata after=capacityMetadata before := by
  obtain ⟨target,budget,table,_,_,called⟩ := compiler_table_branch_success ops law before after index depth lookup accepted
  exact compiler_branch_capacity ops law {before with budget,function:={before.function with jump_tables:=table}}
    after depth 1#u32 false called

theorem TableBranchRun.capacity {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    capacityMetadata after=capacityMetadata before := by
  induction run with
  | done => rfl
  | @cons before middle after index inside called rest ih =>
    exact ih.trans (compiler_table_branch_capacity ops law before middle index before.table_depths.val[index.val]
      (List.getElem?_eq_getElem inside) called)

theorem compiler_lower_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before=.ok (.Ok (),after)) :
    capacityMetadata after=capacityMetadata before := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after accepted
  have retained := run.capacity law
  obtain ⟨budget,code,sources,rfl,_,_⟩ := emission
  exact retained

theorem compiler_br_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    CapacityStep before after state := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state fallback types (.Ok ()) accepted with
  | @live labeled lowered cleared _ _ labelCall reachable lowerCall clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have retained := compiler_lower_table_capacity ops law labeled lowered lowerCall
    have fields : lowered.function.local_slots = before.function.local_slots ∧
        lowered.function.slot_count = before.function.slot_count := by
      rw [frame] at retained
      simpa only [capacityMetadata, Prod.mk.injEq] using retained
    have post := compiler_observe_capacity_bound ops law {lowered with reachable := false, table_depths := cleared} after state (.Ok ()) observed
    exact ⟨post.1.trans fields.1, by simpa only [fields.1, fields.2] using post.2 rfl⟩
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have post := compiler_observe_capacity_bound ops law {labeled with table_depths := cleared} after state (.Ok ()) observed
    rw [frame] at post
    exact ⟨post.1, post.2 rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## GlobalCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem global_get_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (ty : valtype) (dst index : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled
      (globalGetInstruction (decide (width ty = 2)) dst index) = .ok true) :
    dst.val + width ty ≤ compiled.slot_count.val := by
  by_cases vector : width ty = 2
  · simp only [vector,decide_true,globalGetInstruction,ite_true] at checked
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
    have bound := slots_fit_true compiled dst 2#u32 checked
    rw [vector]
    scalar_tac
  · have widthEq : width ty = 1 := by cases ty <;> simp_all [width]
    simp only [widthEq,globalGetInstruction,show decide (1=2) = false from rfl,Bool.false_eq_true,ite_false] at checked
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
    have bound := slots_fit_true compiled dst 1#u32 checked
    rw [widthEq]
    scalar_tac

end Itasca.Runtime.Compiler

end
