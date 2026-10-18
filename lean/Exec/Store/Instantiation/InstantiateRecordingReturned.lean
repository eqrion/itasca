import Exec.Store.Instantiation.InstantiateRecordingErasure
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

/-- Once the inner result is returned, rollback and publication preserve its
actual recorder log verbatim. -/
theorem recordedInstantiateWith_inner_returned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (prior trace : List HostEvent)
    (inner : InstantiateInnerResult M P)
    (returned : recordedInstantiateInner memory hooks floats allocator store module imports platform false prior = .ok (inner,trace)) :
    recordedInstantiateWith memory hooks floats allocator store module imports platform prior =
      (do let out ← runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator store module imports platform
          Result.ok (out,trace)) := by
  have raw : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator store module imports platform false = .ok inner := by
    rw [←recordedInstantiateInner_erase memory hooks floats allocator store module imports platform false prior,returned]
    simp only [bind_ok,Std.uncurry]
  unfold recordedInstantiateWith runtime.store.instantiate.Store.instantiate_with
  rw [returned,raw]
  simp only [bind_ok,Std.uncurry,Std.bind_assoc]
  rcases inner with ⟨result,after,p,committed⟩
  simp only
  repeat' first
    | rfl
    | (apply congrArg (Std.bind _); funext answer)
    | (split <;> simp only [Std.bind_assoc,bind_ok,Std.uncurry])
    | (split_ifs <;> simp only [Std.bind_assoc,bind_ok,Std.uncurry])
end Exec.Store
