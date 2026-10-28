import Exec.Platform.Alloc
import Exec.Platform.Float
import Exec.Platform.Memory

namespace Exec.Platform
open Aeneas Aeneas.Std

/-- The laws of the platform operations used by execution. -/
structure Laws {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) : Prop where
  floatsCorrect : FloatOpsCorrect floats
  allocCorrect : AllocCorrect allocator
  interruptsReturn : ∀ p, hooks.interrupt p ⦃ _ => True ⦄
  memoryLaws : MemoryLaws memory view

end Exec.Platform
