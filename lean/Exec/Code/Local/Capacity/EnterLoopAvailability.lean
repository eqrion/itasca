import Exec.Code.Local.Capacity.EnterAvailability
import Exec.Code.Local.Capacity.EmissionFrameAvailability
import Exec.Code.Local.Capacity.CallbackAvailability

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Live loop opening accepts with one instruction and one control charge.
All control-map and frame storage is independently bounded. -/
theorem compiler_enter_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (scope : ScopeDemand compiler state bound)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (pcRoom : compiler.function.code.length + 1 ≤ U32.max)
    (live : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  have nonempty : alloc.vec.Vec.len state.ctrls ≠ 0#usize := by
    intro same
    have lengthEq := congrArg UScalar.val same
    simp [alloc.vec.Vec.len,controls] at lengthEq
  unfold runtime.compiler.control.FunctionCompiler.enter
  rw [if_neg nonempty]
  step as ⟨last,hlast⟩
  have atLast : last.val = prior.length := by simp [alloc.vec.Vec.len,controls] at hlast; omega
  step as ⟨actual,hactual⟩
  have actualEq : actual = ctrl := by simpa [atLast,controls] using hactual
  rw [actualEq]
  step with block_signature compiler.signatures bt signature selected as ⟨sig,hsig⟩
  subst sig
  step with control_stack_height state.vals.deref ctrl.value_stack_base compiler.function.local_slots
    (by simpa [alloc.vec.Vec.deref] using valuesFit)
    (by simpa [alloc.vec.Vec.deref] using heightFits) as ⟨height,hheight⟩
  have coordinate := scope.coordinate
  step as ⟨source,hsource⟩
  simp only [bind_ok,
    live,Bool.false_eq_true,ite_false,ite_true]
  step with compiler_pc_available ops compiler demand.pc as ⟨status,first,same,pc,accepted,_⟩
  subst first
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,live,ite_true]
  step with compiler_emit_available_frame ops bound available compiler .LoopHead demand.pc demand.codeCapacity
    demand.sourceCapacity demand.codeReserve demand.sourceReserve demand.coordinate demand.instruction
    as ⟨status,emitted,accepted,used,code,sources,frame,usedEq,codeAppend,_⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  change scopePublication ops emitted state .Loop signature height source ctrl.value_stack_base pc none ⦃ out => _ ⦄
  have emittedScope : ScopeDemand emitted state bound := by
    rw [frame]
    refine ⟨?_,scope.coordinate,scope.mapsCapacity,scope.mapsReserve,scope.framesCapacity,
      scope.framesReserve,scope.control,scope.operands,scope.slots⟩
    simpa [alloc.vec.Vec.length,codeAppend] using pcRoom
  have budgetEq : emitted.budget = {compiler.budget with instructions := used} := by rw [frame]
  have firstEffect : CompilationBudgetEffect compiler.budget emitted.budget
      (fun counter => if counter = .instructions then 1 else 0) := by
    rw [budgetEq]
    exact .of_counter .instructions compiler.budget used 1
      (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)
  apply WP.spec_mono (scope_publication_available ops bound available emitted state emittedScope .Loop
    signature height source ctrl.value_stack_base pc none)
  intro out post
  exact ⟨post.1,(firstEffect.trans post.2).weaken (by intro counter; cases counter <;> simp)⟩

end Exec.Code
