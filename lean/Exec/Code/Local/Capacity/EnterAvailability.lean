import Exec.Code.Local.Capacity.ScopePublicationAvailable
import Exec.Code.Local.Capacity.ObserveBudgetAvailability
import Exec.Code.Local.Capacity.BudgetEffects
import Exec.Code.Local.Capacity.EmitAvailability
import Exec.Code.Local.Callbacks.Control.EnterBlock

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

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
  have coordinate := demand.coordinate
  step as ⟨source,hsource⟩
  cases kind
  all_goals
    simp only [bind_ok,Bool.and_eq_true,← ite_and,Bool.false_eq_true,and_false,and_true,
      ite_false,if_false]
    try rw [if_neg (show ¬ compiler.reachable = true from fun active => noThen active rfl)]
    step with compiler_pc_available ops compiler demand.pc as ⟨status,first,same,pc,accepted,_⟩
    subst first
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Bool.and_eq_true,← ite_and,
      Bool.false_eq_true,and_false,and_true,ite_false,if_false]
    try rw [if_neg (show ¬ compiler.reachable = true from fun active => noLoop active rfl)]
    change scopePublication ops compiler state _ signature height source ctrl.value_stack_base pc none ⦃ out => _ ⦄
    exact scope_publication_available ops bound available compiler state demand _ signature height source
      ctrl.value_stack_base pc none

end Exec.Code
