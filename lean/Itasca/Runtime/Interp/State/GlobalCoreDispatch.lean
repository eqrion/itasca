import Itasca.Runtime.Interp.State.GlobalCoreWrite
import Itasca.Runtime.Code.Local.Relations.Global.GlobalLowering
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_globalGet {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex inst function base : Usize) (wide : Bool) (dst index : U32)
    (handler : (if wide then runtime.interp.execute_global_get2 memory exec store inst base dst index
        else runtime.interp.execute_global_get memory exec store inst base dst index) ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Code.globalGetInstruction wide dst index) ⦃ out => Q (out.1,out.2.1,out.2.2.1) ∧ out.2.2.2 = platform ⦄ := by
  have equation : runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Code.globalGetInstruction wide dst index) = (do
        let (result,next,nextStore) ← if wide then runtime.interp.execute_global_get2 memory exec store inst base dst index
          else runtime.interp.execute_global_get memory exec store inst base dst index
        Result.ok (result,next,nextStore,platform)) := by cases wide <;> rfl
  rw [equation]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next,nextStore⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl⟩

theorem dispatch_globalSet {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex inst function base : Usize) (wide : Bool) (src index : U32)
    (handler : (if wide then runtime.interp.execute_global_set2 memory exec store inst base src index
        else runtime.interp.execute_global_set memory exec store inst base src index) ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Code.globalSetInstruction wide src index) ⦃ out => Q (out.1,out.2.1,out.2.2.1) ∧ out.2.2.2 = platform ⦄ := by
  have equation : runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Code.globalSetInstruction wide src index) = (do
        let (result,next,nextStore) ← if wide then runtime.interp.execute_global_set2 memory exec store inst base src index
          else runtime.interp.execute_global_set memory exec store inst base src index
        Result.ok (result,next,nextStore,platform)) := by cases wide <;> rfl
  rw [equation]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next,nextStore⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl⟩
end Itasca.Runtime.Interp
