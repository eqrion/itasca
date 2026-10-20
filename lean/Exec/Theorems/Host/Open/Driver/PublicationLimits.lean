import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Store.Instantiation.InstantiateNoStartLimits
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Supported publication preserves configured invocation capacities, including
rollback and effects committed before a segment-initialization failure. -/
theorem publish_limits {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits) :
    publish memory floats allocator store bytes profile limits ⦃answer=>answer.2.limits=store.limits⦄ := by
  obtain ⟨compiled,actual,_⟩:=WP.spec_imp_exists (Code.compile_with_total allocator allocation bytes profile limits)
  unfold publish
  rw [actual,bind_ok]
  cases compiled with
  | Err error => exact WP.spec.ret rfl
  | Ok module =>
    simp only []
    split
    · rename_i noStart
      obtain ⟨answer,run,shape,accounted,sameToken,limitsEq,issued⟩:=WP.spec_imp_exists
        (Store.instantiate_compiled_no_start_limits memory (inert memory) floats allocator view laws allocation store module
          (Slice.new _) () bytes profile limits actual held.shape held.segmentAccounting (by simp) noStart)
      rw [run,bind_ok]
      rcases answer with ⟨status,after,token⟩
      cases status <;> exact WP.spec.ret limitsEq
    · exact WP.spec.ret rfl
end Exec.Theorems.OpenReentrantControl
