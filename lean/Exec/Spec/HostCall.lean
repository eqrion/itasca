import Exec.Spec.Wf
import Exec.Spec.ExtensionTyping
namespace Exec.Spec
open SpecExt

/-- Typed source arguments make a host-call redex well formed. -/
theorem host_call_wf {s : store} {f : frame} {fa : funcaddr}
    {params : List valtype} {args : List val}
    (source : wf_store s) (ambient : wf_frame f) (typed : ResultsTyped s params args) :
    wf_config ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ := by
  apply wf_config_make source ambient
  apply forall_append (wf_vals (resultsTyped_wf typed))
  intro instruction member
  have same := List.mem_singleton.mp member
  subst instruction
  exact .admininstr_case_70 fa

/-- A host result that passed the concrete type check supplies the independent
host extension's result-typing premise and records the returned source values. -/
theorem host_return_step {s s' : store} {f : frame} {fa : funcaddr} {id : Nat}
    {params results : List valtype} {args returned : List val}
    (host : HostFunction s fa id params results)
    (arguments : ResultsTyped s params args) (extension : Extend_store s s')
    (typed : ResultsTyped s' results returned) (ambient : wf_frame f) :
    StepH ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ [.call fa args (some returned)]
      ⟨⟨s', f⟩, vals returned⟩ := by
  have stores := extend_store_wf extension
  exact .host_return host arguments extension typed
    (host_call_wf stores.1 ambient arguments)
    (wf_config_vals stores.2 ambient (resultsTyped_wf typed))

/-- Explicit host traps and rejected host results share the same atomic source
trap transition, including all callback store effects. -/
theorem host_trap_step {s s' : store} {f : frame} {fa : funcaddr} {id : Nat}
    {params results : List valtype} {args : List val}
    (host : HostFunction s fa id params results)
    (arguments : ResultsTyped s params args) (extension : Extend_store s s')
    (ambient : wf_frame f) :
    StepH ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ [.call fa args none]
      ⟨⟨s', f⟩, [.TRAP]⟩ := by
  have stores := extend_store_wf extension
  exact .host_trap host arguments extension (host_call_wf stores.1 ambient arguments)
    (wf_config_trap stores.2 ambient)
end Exec.Spec
