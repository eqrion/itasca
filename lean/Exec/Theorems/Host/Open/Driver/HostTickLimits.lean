import Exec.Theorems.Host.Callbacks.CallbackCapacities
import Exec.Theorems.Host.Open.Driver.PublicationLimits
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Every actual host-control operation preserves configured invocation limits,
including finite API failure, publication and fresh nested invocation setup. -/
theorem host_tick_limits {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : Store.CodeInterpretation) (select : Selector) (native next : State M)
    (held : ExecutableInv view code native.store) (host : HostState) (mode : native.mode=.host host)
    (actual : tick memory floats allocator select native=.ok (.cont next)) : next.store.limits=native.store.limits := by
  have of_eq {after : State M} (equal : after=next) (same : after.store.limits=native.store.limits) :
      next.store.limits=native.store.limits := by rw [←equal];exact same
  cases selected : host.code[host.pc]? with
  | none =>
    simp only [tick,mode,selected,Result.ok.injEq,ControlFlow.cont.injEq] at actual
    exact of_eq actual rfl
  | some instruction =>
    cases instruction with
    | returned values | trapped | jump target | branch condition yes no =>
      simp only [tick,mode,selected,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      exact of_eq actual rfl
    | returnAction program =>
      obtain ⟨answer,run,permission,effect,owned⟩:=WP.spec_imp_exists
        (program.correct_owned memory allocator allocation view laws code native.store held)
      have limits:=permission.limits
      simp only [tick,mode,selected,run,bind_ok,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      exact of_eq actual limits
    | action program nextPC =>
      obtain ⟨⟨status,after,values⟩,run,permission,effect,owned⟩:=WP.spec_imp_exists
        (program.correct_owned memory allocator allocation view laws code native.store held)
      have limits:=permission.limits
      cases status <;> simp only [tick,mode,selected,run,bind_ok,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      all_goals exact of_eq actual limits
    | publish bytes profile limits nextPC =>
      obtain ⟨⟨status,after⟩,run,sameLimits⟩:=WP.spec_imp_exists
        (publish_limits memory floats allocator allocation view laws code native.store held bytes profile limits)
      cases status <;> simp only [tick,mode,selected,run,bind_ok,Std.uncurry,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      all_goals exact of_eq actual sameLimits
    | invoke index values nextPC =>
      by_cases inside : index.val<native.store.funcs.length
      · simp only [tick,mode,selected,if_pos inside,runtime.interp.Execution.new,bind_ok] at actual
        obtain ⟨phase,run,equal⟩:=Itasca.ResultFacts.bind_ok_inv _ _ _ actual
        simp only [Result.ok.injEq,ControlFlow.cont.injEq] at equal
        exact of_eq equal rfl
      · simp only [tick,mode,selected,if_neg inside,Result.ok.injEq,ControlFlow.cont.injEq] at actual
        exact of_eq actual rfl
end Exec.Theorems.OpenReentrantControl
