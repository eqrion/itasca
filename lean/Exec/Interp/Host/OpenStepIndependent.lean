import Exec.Interp.Host.OpenStep
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

theorem prepareDirect_independent {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (left right : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (inst base : Usize) (func callee : U32)
    (interrupts : ∀p,left.interrupt p=right.interrupt p) :
    prepareDirect memory left floats allocator exec store platform inst base func callee=
      prepareDirect memory right floats allocator exec store platform inst base func callee := by
  have same : prepareCall memory left floats allocator=prepareCall memory right floats allocator := by
    funext e s p address offset
    exact prepareCall_independent memory left right floats allocator e s p address offset interrupts
  simp only [prepareDirect,same]

theorem prepareIndirect_independent {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (left right : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (inst function base : Usize) (entry index callee : U32)
    (interrupts : ∀p,left.interrupt p=right.interrupt p) :
    prepareIndirect memory left floats allocator exec store platform inst function base entry index callee=
      prepareIndirect memory right floats allocator exec store platform inst function base entry index callee := by
  have same : prepareCall memory left floats allocator=prepareCall memory right floats allocator := by
    funext e s p address offset
    exact prepareCall_independent memory left right floats allocator e s p address offset interrupts
  simp only [prepareIndirect,same]

/-- No actual dispatcher case invokes the callback before it has exposed a
pending phase. Only the interrupt component of the dictionary is consulted. -/
theorem prepareDispatch_independent {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (left right : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex inst function base : Usize)
    (instruction : runtime.bytecode.Instr) (interrupts : ∀p,left.interrupt p=right.interrupt p) :
    prepareDispatch memory left floats allocator exec store platform frameIndex inst function base instruction=
      prepareDispatch memory right floats allocator exec store platform frameIndex inst function base instruction := by
  cases instruction
  case LoopHead =>
    simp only [prepareDispatch,runtime.interp.dispatch,runtime.interp.execute_loop_head,runtime.interp.interrupt,interrupts]
  case Call func callee =>
    exact prepareDirect_independent memory left right floats allocator exec store platform inst base func callee interrupts
  case CallIndirect entry index callee =>
    exact prepareIndirect_independent memory left right floats allocator exec store platform inst function base entry index callee interrupts
  all_goals rfl

/-- Native instruction fetch and PC update add no hidden callback dependency. -/
theorem prepareStep_independent {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (left right : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (interrupts : ∀p,left.interrupt p=right.interrupt p) :
    prepareStep memory left floats allocator exec store platform=
      prepareStep memory right floats allocator exec store platform := by
  have same : prepareDispatch memory left floats allocator=prepareDispatch memory right floats allocator := by
    funext e s p frameIndex inst function base instruction
    exact prepareDispatch_independent memory left right floats allocator e s p frameIndex inst function base instruction interrupts
  simp only [prepareStep,same]
end Exec.Interp.OpenCall
