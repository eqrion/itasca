import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit

/-!
Sections, each formerly its own module: DeadOpAvailability, LocalVariableAvailability, StatefulAvailability, BranchLabelAvailability, TransferAvailability, CallAvailability.
-/

/-! ## DeadOpAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every ordinary opcode on a dead input path only observes the validator
stack. No opcode constructor or live operand layout is needed. -/
theorem compiler_dead_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable ≠ true)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val+2*state.vals.length ≤ U32.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  cases compiler with
  | mk signatures params budget batchStart function frames reachable nextSource before height offsets depths =>
    cases reachable with
    | true => exact False.elim (dead rfl)
    | false =>
      let current : runtime.compiler.FunctionCompiler A :=
        ⟨signatures,params,budget,batchStart,function,frames,false,nextSource,before,height,offsets,depths⟩
      change runtime.compiler.FunctionCompiler.observe ops current state ⦃ out =>
        out.1 = .Ok () ∧ out.2.budget = budget ⦄
      exact compiler_observe_available_budget ops bound available current state request slotsFit

end Itasca.Runtime.Compiler

end

/-! ## LocalVariableAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

set_option maxRecDepth 4096 in
theorem lower_local_get_live_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (before : List valtype) (index : U32) (ty : Itasca.wasm_types.ValueType)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (found : compiler.function.locals.val[index.val]? = some ty)
 :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 32#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨localSlot, atSlot, slotPosition⟩ := layout.local_slot index ty found
  have sourceType : (compilerLocals compiler)[index.val]? = some (Itasca.Translate.valueType ty) := by
    simp [compilerLocals, List.getElem?_map, found]
  have different : localSlot ≠ compiler.height := by
    have smaller := layout.local_before_operand_region sourceType
    intro equal
    rw [equal] at slotPosition
    rw [← slotPosition, layout.localSlots, layout.height] at smaller
    omega
  have run := runtime.compiler.lower.FunctionCompiler.op.local_get ops compiler state index 0#u32 0#u128 reachable
  rw [run]
  step as ⟨i, hi⟩
  have iVal : i.val = index.val := by scalar_tac
  have offsetsBound : i.val < compiler.local_offsets.val.length := by rw [iVal]; exact (List.getElem?_eq_some_iff.mp atSlot).1
  step as ⟨src, hsrc⟩
  have srcEq : src = localSlot := by
    simp only [iVal] at hsrc
    exact hsrc.trans (List.getElem?_eq_some_iff.mp atSlot).2
  rw [srcEq]
  step as ⟨j, hj⟩
  have jVal : j.val = index.val := by scalar_tac
  have localsBound : j.val < compiler.function.locals.val.length := by rw [jVal]; exact (List.getElem?_eq_some_iff.mp found).1
  step as ⟨rawType, htype⟩
  have typeEq : rawType = ty := by
    simp only [jVal] at htype
    exact htype.trans (List.getElem?_eq_some_iff.mp found).2
  erw [typeEq, copy_observe_eq ops compiler state ty compiler.height localSlot different]
  exact finish_op_available_effect ops bound available compiler state demand _

set_option maxRecDepth 4096 in
theorem lower_local_write_live_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (before : List valtype) (index : U32) (ty : Itasca.wasm_types.ValueType) (tee : Bool)
    (layout : CompilerLayout compiler (before ++ [Itasca.Translate.valueType ty]))
    (reachable : compiler.reachable = true)
    (found : compiler.function.locals.val[index.val]? = some ty)
 :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if tee then 34#u16 else 33#u16) index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨localSlot, atSlot, slotPosition⟩ := layout.local_slot index ty found
  obtain ⟨operand, operandRead, operandPosition⟩ := last_operand ops compiler before _ layout
  have sourceType : (compilerLocals compiler)[index.val]? = some (Itasca.Translate.valueType ty) := by
    simp [compilerLocals, List.getElem?_map, found]
  have different : operand ≠ localSlot := by
    have smaller := layout.local_before_operand_region sourceType
    intro equal
    rw [← equal] at slotPosition
    rw [← slotPosition, layout.localSlots, operandPosition] at smaller
    omega
  have run := runtime.compiler.lower.FunctionCompiler.op.local_set_or_tee ops compiler state tee index 0#u32 0#u128 reachable
  rw [run]
  step as ⟨i, hi⟩
  have iVal : i.val = index.val := by scalar_tac
  have offsetsBound : i.val < compiler.local_offsets.val.length := by rw [iVal]; exact (List.getElem?_eq_some_iff.mp atSlot).1
  step as ⟨dst, hdst⟩
  have dstEq : dst = localSlot := by
    simp only [iVal] at hdst
    exact hdst.trans (List.getElem?_eq_some_iff.mp atSlot).2
  rw [dstEq, operandRead]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step as ⟨j, hj⟩
  have jVal : j.val = index.val := by scalar_tac
  have localsBound : j.val < compiler.function.locals.val.length := by rw [jVal]; exact (List.getElem?_eq_some_iff.mp found).1
  step as ⟨rawType, htype⟩
  have typeEq : rawType = ty := by
    simp only [jVal] at htype
    exact htype.trans (List.getElem?_eq_some_iff.mp found).2
  rw [typeEq]
  have copyEq := copy_observe_eq ops compiler state ty localSlot operand different
  simp only [core.result.Result.Insts.CoreOpsTry.branch] at copyEq
  erw [copyEq]
  exact finish_op_available_effect ops bound available compiler state demand _

/-- Local accesses in unreachable code only rebuild the observed stack;
valid live accesses use the checked local and operand coordinates above. -/
theorem compiler_local_variable_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (before : List valtype)
    (index : U32) (ty : Itasca.wasm_types.ValueType) (write tee : Bool)
    (layout : compiler.reachable = true → CompilerLayout compiler
      (if write then before ++ [Itasca.Translate.valueType ty] else before))
    (found : compiler.reachable = true → compiler.function.locals.val[index.val]? = some ty) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if write then (if tee then 34#u16 else 33#u16) else 32#u16) index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · cases write
    · exact lower_local_get_live_available ops bound available compiler state demand before index ty
        (layout live) live (found live)
    · exact lower_local_write_live_available ops bound available compiler state demand before index ty tee
        (layout live) live (found live)
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end

/-! ## StatefulAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every reference, table, memory-size/growth, and bulk-memory callback
accepts from its source signature and independently bounded storage. Pair
storage is charged only for table.copy and table.init. -/
theorem compiler_stateful_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (op : SourceMachine.Stateful.Instruction)
    (signature : SourceMachine.Stateful.Signature C op input output) (a b : U32)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (pairIndex : statefulUsesPair op = true → compiler.function.indirect.length ≤ U32.max)
    (pairCapacity : statefulUsesPair op = true → compiler.function.indirect.length < Usize.max)
    (pairReserve : statefulUsesPair op = true → compiler.function.indirect.length + 1 ≤ bound) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (statefulOpcode op) a b 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨first,second,reads,_,_⟩ := stateful_operands ops compiler C front input output op signature (layout live)
    by_cases paired : statefulUsesPair op = true
    · obtain ⟨⟨status,after⟩,actual,index,pairs,accepted,_,frame,_⟩ := WP.spec_imp_exists
        (compiler_pair_available ops bound available compiler a b
          (pairIndex paired) (pairCapacity paired) (pairReserve paired))
      dsimp only at accepted frame
      subst status
      have read : runtime.compiler.FunctionCompiler.operand ops after 3#usize = .ok (.Ok first) := by
        rw [frame]
        have arity : op.arity = 3 := by cases op <;> simp_all [statefulUsesPair,SourceMachine.Stateful.Instruction.arity]
        simpa [StatefulReads,arity,statefulDepth,runtime.compiler.FunctionCompiler.operand.eq] using reads.1
      rw [lower_stateful_pair_eq ops compiler after state op first second a b index live paired actual read]
      have afterDemand : CallbackDemand after state bound := by
        rw [frame]
        exact ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,
          demand.sourceReserve,demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
      have budget : after.budget = compiler.budget := by rw [frame]
      simpa only [budget] using finish_op_available_effect ops bound available after state afterDemand
        (statefulInstruction op first second a index)
    · have single : statefulUsesPair op = false := Bool.eq_false_iff.mpr paired
      rw [lower_stateful_eq ops compiler state op first second a b 0#u32 live single reads]
      exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end

/-! ## BranchLabelAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Each streamed branch-table label, including the default label, accepts
from independent branch budget and scratch-vector bounds. -/
theorem compiler_branch_label_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (depth : U32)
    (room : compiler.budget.branches.val < compiler.budget.limits.max_branch_table_entries.val)
    (capacity : compiler.table_depths.length < Usize.max)
    (request : compiler.table_depths.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state depth
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
          (fun counter => if counter = .branches then 1 else 0) ∧
        out.2.table_depths.val = compiler.table_depths.val ++ [depth] ⦄ := by
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.available
    ops bound available compiler state depth room capacity request)
  rintro ⟨status, after⟩ ⟨accepted, used, frame, usedEq, appended⟩
  refine ⟨accepted, ?_, appended⟩
  rw [frame]
  exact CompilationBudgetEffect.of_counter .branches compiler.budget used 1
    (by change compiler.budget.branches.val ≤ used.val; omega)
    (by change used.val ≤ compiler.budget.branches.val + 1; omega)

end Itasca.Runtime.Compiler

end

/-! ## TransferAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

end Itasca.Runtime.Compiler

end

/-! ## CallAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Direct calls accept from their captured source parameter width and typed
argument layout. Checked subtraction is discharged from the layout. -/
theorem compiler_call_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front params : List valtype)
    (index paramSlots : U32)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ params))
    (signature : compiler.reachable = true → compiler.func_param_slots.val[index.val]? = some paramSlots)
    (parameterWidth : paramSlots.val = slots params) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.call ops compiler state index 0#u32 0#u128 live
    rw [run]
    step as ⟨i,hi⟩
    have atIndex : i.val = index.val := by scalar_tac
    have inRange : i.val < compiler.func_param_slots.length := by
      have found := (List.getElem?_eq_some_iff.mp (signature live)).1
      simpa [atIndex] using found
    step as ⟨slots,hslots⟩
    have same : slots = paramSlots := by
      simp only [atIndex] at hslots
      exact hslots.trans (List.getElem?_eq_some_iff.mp (signature live)).2
    rw [same]
    have height := (layout live).height
    simp only [slots_append] at height
    step as ⟨o,ho⟩
    cases o with
    | none => simp only at ho; omega
    | some base =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact finish_op_available_effect ops bound available compiler state demand _
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Indirect calls additionally reserve one pair descriptor. Their parameter
and table-index arithmetic follows from the independently typed live stack. -/
theorem compiler_indirect_call_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front params : List valtype)
    (a b : U32) (signature : runtime.compiler.Signature)
    (layout : compiler.reachable = true → CompilerLayout compiler ((front ++ params) ++ [.I32]))
    (metadata : compiler.reachable = true → compiler.signatures.val[a.val]? = some signature)
    (parameterWidth : signature.param_slots.val = slots params)
    (pairIndex : compiler.function.indirect.length ≤ U32.max)
    (pairCapacity : compiler.function.indirect.length < Usize.max)
    (pairReserve : compiler.function.indirect.length + 1 ≤ bound) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 17#u16 a b 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_indirect_call_dispatch ops compiler state a b live]
    unfold indirectCallLowering
    step as ⟨i,hi⟩
    have atIndex : i.val = a.val := by scalar_tac
    have inRange : i.val < compiler.signatures.length := by
      have found := (List.getElem?_eq_some_iff.mp (metadata live)).1
      simpa [atIndex] using found
    step as ⟨sig,hsig⟩
    have same : sig = signature := by
      simp only [atIndex] at hsig
      exact hsig.trans (List.getElem?_eq_some_iff.mp (metadata live)).2
    rw [same]
    have height := (layout live).height
    simp only [slots_append,slots,width,Nat.add_zero] at height
    have maximum := compiler.height.hmax
    step as ⟨o,ho⟩
    cases o with
    | none => simp only at ho; scalar_tac
    | some total =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have totalWidth : total.val = signature.param_slots.val + 1 := by simp only at ho; omega
      step as ⟨o,ho⟩
      cases o with
      | none => simp only at ho; omega
      | some base =>
        simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step with compiler_pair_available ops bound available compiler b a pairIndex pairCapacity pairReserve
          as ⟨status,paired,index,pairs,accepted,_,frame,_⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        obtain ⟨operand,read,_⟩ := last_operand ops compiler (front ++ params) .I32 (layout live)
        have pairedRead : runtime.compiler.FunctionCompiler.operand ops paired 1#usize = .ok (.Ok operand) := by
          rw [frame]
          simpa only [runtime.compiler.FunctionCompiler.operand.eq] using read
        rw [pairedRead]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        have afterDemand : CallbackDemand paired state bound := by
          rw [frame]
          exact ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,
            demand.sourceReserve,demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
        have budget : paired.budget = compiler.budget := by rw [frame]
        simpa only [budget] using finish_op_available_effect ops bound available paired state afterDemand
          (.CallIndirect index operand base)
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end
