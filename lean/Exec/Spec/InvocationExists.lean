import Exec.Spec.Invocation
import Exec.Spec.Wf
namespace Exec.Spec
open SpecExt

/-- Source invocation exists for any well-formed argument values and in-range
function address. It does not require argument types or arity to match. -/
theorem invocation_exists {s : store} (valid : wf_store s) (address : Nat)
    (bound : address < s.FUNCS.length) (args : List val) (values : Forall wf_val args) :
    ∃initial,fun_invoke s address args initial := by
  have ambient : wf_frame invocationFrame := by
    constructor
    · simp [invocationFrame,Forall]
    · constructor <;> simp [invocationFrame,Forall]
  have configWf : wf_config ⟨⟨s,invocationFrame⟩,vals args++[.CALL_ADDR address]⟩ := by
    apply wf_config_make valid ambient
    apply forall_append (wf_vals values)
    intro instruction member
    have same := List.mem_singleton.mp member
    subst instruction
    exact .admininstr_case_70 address
  cases signature : s.FUNCS[address]!.TYPE with
  | mk_functype params results =>
    cases params with | mk_list params =>
      cases results with | mk_list results =>
        refine ⟨⟨⟨s,invocationFrame⟩,vals args++[.CALL_ADDR address]⟩,?_⟩
        exact .fun_invoke_case_0 s address args.length args invocationFrame params results
          rfl bound signature configWf ambient (.state_case_0 _ _ valid ambient) rfl
end Exec.Spec
