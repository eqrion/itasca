import Exec.Spec.Choices.HostChoices
import Exec.Interp.Host.HostResume
import Exec.Representation.Store
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The source reply of one returned callback, after the actual dynamic result
check. Invalid results and host errors trap while retaining callback effects. -/
noncomputable def checkedHostReply {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (after : runtime.store.Store M)
    (signature : Itasca.types.FuncType) (results : alloc.vec.Vec runtime.Value)
    (status : core.result.Result Unit runtime.platform.HostError) : Spec.HostReply := by
  classical
  exact ⟨Store.decodeStore view code after,
    if status=.Ok () ∧ runtime.interp.check_values memory after results.slice signature.results.slice=.ok (.Ok ())
    then some (results.val.map sourceValue) else none⟩
end Exec.Theorems
