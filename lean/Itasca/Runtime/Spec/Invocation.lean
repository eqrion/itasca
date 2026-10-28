import Itasca.Runtime.Spec.Context
namespace Itasca.Runtime.Spec
open SpecExt

/-- The generated invocation judgment fixes the ambient frame to the empty
module instance and emits the argument constants followed by CALL_ADDR. -/
def invocationFrame : frame := ⟨[], ⟨[], [], [], [], [], [], [], []⟩⟩

theorem invocation_config {s : store} {address : funcaddr} {args : List val} {initial : config}
    (invoked : fun_invoke s address args initial) :
    initial = ⟨⟨s, invocationFrame⟩, vals args ++ [.CALL_ADDR address]⟩ := by
  cases invoked
  simp_all [invocationFrame, vals, Map]

theorem invocation_frame_wf {s : store} {address : funcaddr} {args : List val} {initial : config}
    (invoked : fun_invoke s address args initial) : wf_frame invocationFrame := by
  cases invoked
  assumption
end Itasca.Runtime.Spec
