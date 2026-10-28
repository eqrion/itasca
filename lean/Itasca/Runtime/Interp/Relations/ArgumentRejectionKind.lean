import Itasca.Runtime.Interp.Relations.Arguments
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem checkArgument_error_kind {id value ty error}
    (rejected : checkArgument id value ty = .Err error) :
    error = .BadArguments ∨ error = .WrongStore := by
  unfold checkArgument at rejected
  split at rejected
  · split at rejected <;> simp_all
  · simp_all

theorem checkArguments_error_kind {id values types error}
    (rejected : checkArguments id values types = .Err error) :
    error = .BadArguments ∨ error = .WrongStore := by
  induction values generalizing types with
  | nil => cases types <;> simp_all [checkArguments]
  | cons value values ih =>
    cases types with
    | nil => simp_all [checkArguments]
    | cons ty types =>
      cases checked : checkArgument id value ty with
      | Ok unitValue => exact ih (by simpa only [checkArguments,checked] using rejected)
      | Err failed =>
        have same : failed = error := by simpa only [checkArguments,checked,core.result.Result.Err.injEq] using rejected
        subst failed
        exact checkArgument_error_kind checked

theorem check_values_error_kind {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (args : Slice runtime.Value) (types : Slice Itasca.types.ValueType)
    (error : runtime.ExecError)
    (rejected : runtime.interp.check_values memory store args types = .ok (.Err error)) :
    error = .BadArguments ∨ error = .WrongStore := by
  have decision := check_values_effect memory store args types
  rw [rejected,WP.spec_ok] at decision
  split at decision
  · exact checkArguments_error_kind decision.symm
  · simpa only [core.result.Result.Err.injEq] using Or.inl decision
end Itasca.Runtime.Interp
