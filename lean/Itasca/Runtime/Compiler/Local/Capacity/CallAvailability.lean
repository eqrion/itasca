import Itasca.Runtime.Compiler.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Calls.LoweringCall
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallLowering
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal

namespace Itasca.Runtime.Code
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
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128 = (do
      let i ← lift (UScalar.cast .Usize index)
      let slots ← Slice.index_usize compiler.func_param_slots i
      let o ← lift (U32.checked_sub compiler.height slots)
      let r ← core.option.Option.ok_or o Itasca.error.VisitError.OutOfMemory
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Call index val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (r1, compiler)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos live]
      rfl
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
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
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
          simpa only [runtime.compiler.FunctionCompiler.operand] using read
        rw [pairedRead]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        have afterDemand : CallbackDemand paired state bound := by
          rw [frame]
          exact ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,
            demand.sourceReserve,demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
        have budget : paired.budget = compiler.budget := by rw [frame]
        simpa only [budget] using finish_op_available_effect ops bound available paired state afterDemand
          (.CallIndirect index operand base)
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
