import Itasca.Runtime.Compiler.Local.Capacity.EnterAvailability
import Itasca.Runtime.Compiler.Local.Capacity.EmissionFrameAvailability
import Itasca.Runtime.Compiler.Local.Capacity.CallbackAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal

/-!
Availability of block, loop and if entry callbacks under source stack bounds. The common theorem retains the branch-specific allocation premises.
-/

/-! ## Enter If Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Live if opening accepts with one instruction and one control charge.
All control-map and frame storage is independently bounded. -/
theorem compiler_enter_if_available {A : Type} (ops : runtime.platform.Alloc A)
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
    (front : List valtype) (layout : CompilerLayout compiler (front ++ [.I32]))
    (live : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt ⦃ out =>
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
  obtain ⟨condition,read,_⟩ := last_operand ops compiler front .I32 layout
  rw [read]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with compiler_emit_available_frame ops bound available compiler (.JumpIfZero condition core.num.U32.MAX)
    demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
    demand.coordinate demand.instruction
    as ⟨status,emitted,accepted,used,code,sources,frame,usedEq,codeAppend,_⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have emittedPc : emitted.function.code.length ≤ U32.max := by
    rw [frame]
    simpa [alloc.vec.Vec.length,codeAppend] using pcRoom
  step with compiler_pc_available ops emitted emittedPc as ⟨status,first,same,pc,accepted,_⟩
  subst first
  rw [accepted]
  have emittedLive : emitted.reachable = true := by rw [frame]; exact live
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Bool.false_eq_true,ite_false,ite_self]
  change scopePublication ops emitted state .Then signature height source ctrl.value_stack_base pc
    (some (alloc.vec.Vec.len compiler.function.code)) ⦃ out => _ ⦄
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
  apply WP.spec_mono (scope_publication_available ops bound available emitted state emittedScope .Then
    signature height source ctrl.value_stack_base pc (some (alloc.vec.Vec.len compiler.function.code)))
  intro out post
  exact ⟨post.1,(firstEffect.trans post.2).weaken (by intro counter; cases counter <;> simp)⟩

end Itasca.Runtime.Compiler

end

/-! ## Enter Loop Availability -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Scope Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every raw observed stack entry occupies at most two compiler words. -/
theorem stack_words_le_twice_length (values : List Itasca.code.StackType) :
    stackWords values ≤ 2*values.length := by
  induction values with
  | nil => simp [stackWords]
  | cons value rest ih =>
    have widthBound : compilerStackWidth value ≤ 2 := by
      cases value with
      | Bot => decide
      | Val ty => cases ty <;> decide
    simp only [stackWords,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    omega

/-- All scope kinds accept under source control/signature information and
independent demands. Live if entry alone needs a condition layout; dead code
requires no live operand layout. Scope height arithmetic follows from the
same conservative slot bound used by ordinary callbacks. -/
theorem compiler_enter_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (scope : ScopeDemand compiler state bound)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (pcRoom : compiler.function.code.length + 1 ≤ U32.max)
    (conditionLayout : compiler.reachable = true → kind = .Then →
      ∃ front, CompilerLayout compiler (front ++ [.I32])) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  have heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max := by
    have words := stack_words_le_twice_length (state.vals.val.take ctrl.value_stack_base.val)
    have lengthBound : (state.vals.val.take ctrl.value_stack_base.val).length ≤ state.vals.val.length := by
      simp only [List.length_take]; exact Nat.min_le_right _ _
    have room := scope.slots
    simp only [alloc.vec.Vec.length] at room
    omega
  by_cases loopEntry : compiler.reachable = true ∧ kind = .Loop
  · obtain ⟨live,rfl⟩ := loopEntry
    exact compiler_enter_loop_available ops bound available compiler state demand scope ctrl prior bt signature
      controls selected valuesFit heightFits pcRoom live
  · by_cases ifEntry : compiler.reachable = true ∧ kind = .Then
    · obtain ⟨live,rfl⟩ := ifEntry
      obtain ⟨front,layout⟩ := conditionLayout live rfl
      exact compiler_enter_if_available ops bound available compiler state demand scope ctrl prior bt signature
        controls selected valuesFit heightFits pcRoom front layout live
    · apply WP.spec_mono (compiler_enter_without_emission_available ops bound available compiler state scope ctrl prior
        kind bt signature controls selected valuesFit heightFits
        (by intro live same; exact ifEntry ⟨live,same⟩)
        (by intro live same; exact loopEntry ⟨live,same⟩))
      intro out post
      exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩

end Itasca.Runtime.Compiler

end
