import Exec.Code.Local.Capacity.CloseBodyAvailability
import Exec.Code.Local.Capacity.ScopeCloseAvailability
import Exec.Code.Local.Capacity.GuardedScopeCloseAvailability
import Exec.Code.Local.Capacity.CallbackCapacity

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
