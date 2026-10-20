import Exec.Code.Local.Capacity.EnterLoopAvailability
import Exec.Code.Local.Capacity.EnterIfAvailability

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Every raw observed stack entry occupies at most two compiler words. -/
theorem stackWords_le_twice_length (values : List Itasca.code.StackType) :
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
    have words := stackWords_le_twice_length (state.vals.val.take ctrl.value_stack_base.val)
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

end Exec.Code
