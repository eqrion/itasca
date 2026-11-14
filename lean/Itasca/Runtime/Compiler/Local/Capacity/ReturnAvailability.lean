import Itasca.Runtime.Compiler.Local.Lowering.Control.ReturnContracts
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts

/-!
Sections, each formerly its own module: EndDispatchAvailability, EnterAvailability, ScopeAvailability, ReturnAvailability.
-/

/-! ## EndDispatchAvailability -/

section

/-!
Availability of end callbacks for root bodies, ordinary scopes and guarded scopes. The dispatch proof retains each scope-specific allocation obligation.
-/

/-! ## Close Body Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Root closing accepts from retained branch-hole shapes and map ownership.
The implicit epilogue consumes one instruction, including for dead bodies. -/
theorem compiler_close_body_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Body .Empty ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ branch old, compiler.function.code.val[guard.val]? = some (BranchKind.instruction branch old) := by
    intro guard h
    rw [noIf] at h
    contradiction
  have pcFits : compiler.function.code.length ≤ U32.max := by
    scalar_tac
  have space : frame.kind = .Body → compiler.function.code.length < Usize.max ∧
      compiler.function.source_offsets.length < Usize.max ∧
      compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max ∧
      compiler.function.code.length + 1 ≤ bound ∧ compiler.function.source_offsets.length + 1 ≤ bound ∧
      compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val := by
    intro _
    exact ⟨demand.codeCapacity, demand.sourceCapacity, demand.coordinate, demand.codeReserve,
      demand.sourceReserve, demand.instruction⟩
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.available
    ops bound available compiler state .Body .Empty
    ⟨frame, rest, frames, branches, guardSites, mapFits, coordinateFits, pcFits,
      demand.operands, demand.slots, space⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have usedEqOne : used.val = compiler.budget.instructions.val + 1 := by
    simpa [kind] using usedEq
  refine ⟨rfl, ?_⟩
  rw [budgetEq]
  exact CompilationBudgetEffect.of_counter .instructions compiler.budget used 1
    (by simp [ChargeCounter.used] at usedEqOne ⊢; omega)
    (by simp [ChargeCounter.used] at usedEqOne ⊢; omega)

end Itasca.Runtime.Compiler

end

/-! ## Guarded Scope Close Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Non-root scope closing accepts from retained holes, map ownership, and
independent observer demand, preserving every compiler resource counter. -/
theorem compiler_close_guarded_scope_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (guard : Usize) (condition old : U32)
    (nonBody : frame.kind ≠ .Body) (hasIf : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ branch old, compiler.function.code.val[guard.val]? = some (BranchKind.instruction branch old) := by
    intro queried h
    have same : queried = guard := Option.some.inj (h.symm.trans hasIf)
    subst queried
    exact ⟨.zero condition, old, by simpa [BranchKind.instruction] using guardCode⟩
  have pcFits : compiler.function.code.length ≤ U32.max := by
    scalar_tac
  have space : frame.kind = .Body → compiler.function.code.length < Usize.max ∧
      compiler.function.source_offsets.length < Usize.max ∧
      compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max ∧
      compiler.function.code.length + 1 ≤ bound ∧ compiler.function.source_offsets.length + 1 ≤ bound ∧
      compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val := by
    intro body
    exact False.elim (nonBody body)
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.available
    ops bound available compiler state .Block .Empty
    ⟨frame, rest, frames, branches, guardSites, mapFits, coordinateFits, pcFits, request, slotsFit, space⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have countZero : (match frame.kind with | .Body => 1 | _ => 0) = 0 := by
    cases kindEq : frame.kind <;> simp_all
  have usedEqOld : used.val = compiler.budget.instructions.val := by
    simpa [countZero] using usedEq
  have usedSame : used = compiler.budget.instructions := by
    apply UScalar.eq_of_val_eq
    exact usedEqOld
  rw [budgetEq, usedSame]
  exact ⟨rfl, rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Scope Close Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Non-root scope closing accepts from retained holes, map ownership, and
independent observer demand, preserving every compiler resource counter. -/
theorem compiler_close_scope_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (nonBody : frame.kind ≠ .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ branch old, compiler.function.code.val[guard.val]? = some (BranchKind.instruction branch old) := by
    intro guard h
    rw [noIf] at h
    contradiction
  have pcFits : compiler.function.code.length ≤ U32.max := by
    scalar_tac
  have space : frame.kind = .Body → compiler.function.code.length < Usize.max ∧
      compiler.function.source_offsets.length < Usize.max ∧
      compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max ∧
      compiler.function.code.length + 1 ≤ bound ∧ compiler.function.source_offsets.length + 1 ≤ bound ∧
      compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val := by
    intro body
    exact False.elim (nonBody body)
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.available
    ops bound available compiler state .Block .Empty
    ⟨frame, rest, frames, branches, guardSites, mapFits, coordinateFits, pcFits, request, slotsFit, space⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have countZero : (match frame.kind with | .Body => 1 | _ => 0) = 0 := by
    cases kindEq : frame.kind <;> simp_all
  have usedEqOld : used.val = compiler.budget.instructions.val := by
    simpa [countZero] using usedEq
  have usedSame : used = compiler.budget.instructions := by
    apply UScalar.eq_of_val_eq
    exact usedEqOld
  rw [budgetEq, usedSame]
  exact ⟨rfl, rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## End Dispatch Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every end callback accepts from retained scope ownership and independent
capacity, including the nonvoid dead-body epilogue. Target PCs are constructed
from numeric bounds; source guard/fixup shapes discharge actual patching. -/
theorem compiler_end_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1)
    (frame : runtime.compiler.Frame) (rest : alloc.vec.Vec runtime.compiler.Frame)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (rootNoGuard : frame.kind = .Body → frame.if_pc = none)
    (guardOwned : ∀ guard, frame.if_pc = some guard → ∃ condition old,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have fits : compiler.function.code.length < 2^UScalarTy.U32.numBits := by
    have room := capacity.pc
    scalar_tac
  let target := U32.ofNatCore compiler.function.code.length fits
  have position : target.val = compiler.function.code.val.length := U32.ofNatCore_val_eq fits
  by_cases root : frame.kind = .Body
  · exact compiler_close_body_available ops bound available compiler state (capacity.one (by decide))
      frame rest target frames root (rootNoGuard root) position branches mapFits coordinateFits
  · cases guardPc : frame.if_pc with
    | none =>
      apply WP.spec_mono (compiler_close_scope_available ops bound available compiler state frame rest target frames root
        guardPc position branches mapFits coordinateFits capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
    | some guard =>
      obtain ⟨condition,old,guardCode⟩ := guardOwned guard guardPc
      apply WP.spec_mono (compiler_close_guarded_scope_available ops bound available compiler state frame rest target frames
        guard condition old root guardPc guardCode position branches mapFits coordinateFits capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end

end

/-! ## EnterAvailability -/

section

/-!
Allocation availability for scope publication and entry without emitted code. The publication reserve is discharged before constructing the entered compiler state.
-/

/-! ## Enter Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Exact entry counters imply the independent compilation budget bounds. -/
theorem EnterBudget.compilation_effect {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (kind : code.LabelKind) (effect : EnterBudget before after kind) :
    CompilationBudgetEffect before.budget after.budget (fun counter =>
      match counter with
      | .instructions => enterInstructionCharge before.reachable kind
      | .controls => 1
      | _ => 0) := by
  obtain ⟨instructions, controls, same, instructionsEq, controlsEq⟩ := effect
  rw [same]
  refine ⟨rfl, rfl, ?_⟩
  intro counter
  cases counter <;> simp only [ChargeCounter.used] <;> constructor <;> omega

/-- Opening an ordinary block or a dead scope accepts without emitting code.
Its budget effect is exactly one control, with all other counters retained. -/
theorem compiler_enter_without_emission_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : ScopeDemand compiler state bound) (ctrl : Itasca.code.Ctrl)
    (prior : List Itasca.code.Ctrl) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (noThen : compiler.reachable = true → kind ≠ .Then)
    (noLoop : compiler.reachable = true → kind ≠ .Loop) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .controls then 1 else 0) ⦄ := by
  clear heightFits -- The scope demand supplies the stronger whole-stack bound.
  refine WP.spec_mono (runtime.compiler.control.FunctionCompiler.enter.available ops bound available compiler state kind bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit⟩ ?_ ?_) ?_
  · refine ⟨demand.pc, ?_, demand.coordinate, demand.mapsCapacity, demand.mapsReserve,
      demand.framesCapacity, demand.framesReserve, demand.control, demand.operands, demand.slots, ?_⟩
    · intro live thenKind
      exact False.elim (noThen live thenKind)
    · intro live emitted
      rcases emitted with thenKind | loopKind
      · exact False.elim (noThen live thenKind)
      · exact False.elim (noLoop live loopKind)
  · intro live thenKind
    exact False.elim (noThen live thenKind)
  · intro out post
    refine ⟨post.1, (EnterBudget.compilation_effect compiler out.2 kind post.2).weaken ?_⟩
    have zero : enterInstructionCharge compiler.reachable kind = 0 := by
      cases active : compiler.reachable with
      | false => simp [enterInstructionCharge]
      | true => cases kind <;> simp_all [enterInstructionCharge]
    intro counter
    cases counter <;> simp [zero]

end Itasca.Runtime.Compiler

end

end

/-! ## ScopeAvailability -/

section

/-!
Availability of block, loop and if entry callbacks under source stack bounds. The common theorem retains the branch-specific allocation premises.
-/

/-! ## Enter If Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

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
  clear heightFits -- The scope demand supplies the stronger whole-stack bound.
  refine WP.spec_mono (runtime.compiler.control.FunctionCompiler.enter.available ops bound available compiler state .Then bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit⟩ ?_ ?_) ?_
  · exact ⟨scope.pc, fun _ _ => pcRoom, scope.coordinate, scope.mapsCapacity, scope.mapsReserve,
      scope.framesCapacity, scope.framesReserve, scope.control, scope.operands, scope.slots,
      fun _ _ => ⟨demand.codeCapacity, demand.sourceCapacity, demand.codeReserve,
        demand.sourceReserve, demand.instruction⟩⟩
  · intro _ _
    obtain ⟨condition, called, _⟩ := last_operand ops compiler front .I32 layout
    exact ⟨condition, called⟩
  · intro out post
    refine ⟨post.1, (EnterBudget.compilation_effect compiler out.2 .Then post.2).weaken ?_⟩
    intro counter
    cases counter <;> simp [enterInstructionCharge, live]

end Itasca.Runtime.Compiler

end

/-! ## Enter Loop Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

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
  clear heightFits -- The scope demand supplies the stronger whole-stack bound.
  refine WP.spec_mono (runtime.compiler.control.FunctionCompiler.enter.available ops bound available compiler state .Loop bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit⟩ ?_ ?_) ?_
  · exact ⟨scope.pc, fun _ _ => pcRoom, scope.coordinate, scope.mapsCapacity, scope.mapsReserve,
      scope.framesCapacity, scope.framesReserve, scope.control, scope.operands, scope.slots,
      fun _ _ => ⟨demand.codeCapacity, demand.sourceCapacity, demand.codeReserve,
        demand.sourceReserve, demand.instruction⟩⟩
  · intro _ impossible
    cases impossible
  · intro out post
    refine ⟨post.1, (EnterBudget.compilation_effect compiler out.2 .Loop post.2).weaken ?_⟩
    intro counter
    cases counter <;> simp [enterInstructionCharge, live]

end Itasca.Runtime.Compiler

end

/-! ## Scope Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

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

end

/-! ## ReturnAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Return accepts from a retained root frame and a source-justified result
width. Dead returns need neither a live root lookup nor result operands. -/
theorem compiler_return_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (body : runtime.compiler.Frame)
    (bodyFrame : compiler.reachable = true → compiler.frames.val[0]? = some body)
    (height : compiler.reachable = true → body.results.val ≤ compiler.height.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.available ops bound available compiler state demand body bodyFrame height)
  rintro ⟨status, after⟩ ⟨accepted, used, frame, usedEq⟩
  dsimp only at frame usedEq ⊢
  rw [frame]
  refine ⟨accepted, .of_counter .instructions compiler.budget used 1 ?_ ?_⟩
  · simp only [ChargeCounter.used]
    split at usedEq <;> scalar_tac
  · simp only [ChargeCounter.used]
    split at usedEq <;> scalar_tac

end Itasca.Runtime.Compiler

end
