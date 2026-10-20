import Exec.Theorems.Host.Callbacks.CallbackActions
import Exec.Store.Api.GrowthLimits
namespace Exec.Theorems
open Aeneas Aeneas.Std

theorem StoreCallbacks.WriteI32Result.limits {M : Type} {before after : runtime.store.Store M}
    {index value accepted} (effect : WriteI32Result before index value accepted after) :
    after.limits=before.limits := by cases effect <;> rfl

theorem StoreCallbacks.Returns.limits {M : Type} {program before status after values}
    (source : @Returns M program before status after values) : after.limits=before.limits := by
  induction source with
  | terminal => rfl
  | write effect tail ih => exact ih.trans effect.limits
  | rejected effect => exact effect.limits
  | yes source ih | no source ih => exact ih

theorem AllocationCallbacks.DefineHostResult.limits {M : Type} {before after : runtime.store.Store M}
    {signature identity accepted} (effect : DefineHostResult before signature identity accepted after) :
    after.limits=before.limits := by
  have intern {status after} (effect : Store.InternEffect before signature (status,after)) :
      after.limits=before.limits := by
    rcases effect with ⟨error,same⟩ | ⟨index,lookup,same⟩ | ⟨types,count,appended,absent,room,total,bounded,same⟩
    all_goals exact congrArg (fun answer => answer.2.limits) same
  cases effect with
  | intern_failed effect | refused effect => exact intern effect
  | published effect room appended =>
    have same := intern effect
    exact same

theorem AllocationCallbacks.Returns.limits {M : Type} {program before status after values}
    (source : @Returns M program before status after values) : after.limits=before.limits := by
  induction source with
  | base source => exact source.limits
  | published effect tail ih => exact ih.trans effect.limits
  | refused effect => exact effect.limits
  | yes source ih | no source ih => exact ih

theorem ReadCallbacks.Returns.limits {M : Type} {program before status after values}
    (source : @Returns M program before status after values) : after.limits=before.limits := by
  induction source with
  | base source => exact source.limits
  | global | global_invalid | table | table_invalid | table_bounds => rfl
  | sequence first tail ih => exact ih.trans first.limits
  | rejected first => exact first.limits
  | yes source ih | no source ih => exact ih

theorem GrowthCallbacks.Returns.limits {M : Type} {view : M → Slice U8} {code program before status after values}
    (source : Returns view code program before status after values) : after.limits=before.limits := by
  induction source with
  | base source => exact source.limits
  | sequence first tail ih => exact ih.trans first.limits
  | rejected first => exact first.limits
  | memory inside effect tail ih | table inside effect tail ih => exact ih.trans effect.limits
  | memory_invalid | table_invalid => rfl
  | yes source ih | no source ih => exact ih

/-- Checked API segments preserve configured invocation capacities on success
and rejection, including partial allocation and mutation before a host trap. -/
theorem CallbackActions.Returns.limits {M : Type} {view : M → Slice U8} {code program before status after values}
    (source : Returns view code program before status after values) : after.limits=before.limits := by
  induction source with
  | read source | growth source | allocation source => exact source.limits
  | sequence first tail ihFirst ihTail => exact ihTail.trans ihFirst
  | rejected first ih => exact ih
  | yes source ih | no source ih => exact ih
end Exec.Theorems
