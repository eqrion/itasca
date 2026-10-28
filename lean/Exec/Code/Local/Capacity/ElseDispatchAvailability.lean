import Exec.Code.Local.Capacity.ElseAvailability
import Exec.Code.Local.Capacity.CallbackCapacity

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

private theorem representable_pc (count : Nat) (bounded : count ≤ U32.max) :
    ∃ pc : U32, pc.val = count := by
  have fits : count < 2^UScalarTy.U32.numBits := by scalar_tac
  exact ⟨U32.ofNatCore count fits,U32.ofNatCore_val_eq fits⟩

/-- Every valid else state accepts. Numeric capacity constructs the target
PC; retained guard ownership and entry metadata discharge the live/dead cases.
No successful callback equation is supplied by the caller. -/
theorem compiler_else_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (liveGuard : compiler.reachable = true → frame.if_pc ≠ none)
    (guardOwned : ∀ guard, frame.if_pc = some guard → ∃ condition,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨target,position⟩ := representable_pc (compiler.function.code.length+1) capacity.pc
    cases guardPc : frame.if_pc with
    | none => exact False.elim (liveGuard live guardPc)
    | some guard =>
      obtain ⟨condition,guardCode⟩ := guardOwned guard guardPc
      exact compiler_else_live_available ops bound available compiler state (capacity.one (by decide)) bt
        frame prior guard condition target frames live guardPc guardCode position fixupsCapacity fixupsReserve
  · have dead : compiler.reachable = false := Bool.eq_false_iff.mpr live
    cases guardPc : frame.if_pc with
    | none =>
      apply WP.spec_mono (compiler_else_unentered_available ops bound available compiler state bt frame prior frames
        dead guardPc capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
    | some guard =>
      obtain ⟨condition,guardCode⟩ := guardOwned guard guardPc
      obtain ⟨target,position⟩ := representable_pc compiler.function.code.length (by have room := capacity.pc; omega)
      apply WP.spec_mono (compiler_else_dead_available ops bound available compiler state bt frame prior guard condition
        target frames dead guardPc guardCode position capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
