import Exec.Spec.Typing.ValueConfigTyping
import Exec.Spec.Typing.EmptyFrameTyping
import Exec.Spec.Invocation

/-! Source invocation typing uses matching argument types, in addition to the
well-formedness and address bounds required by the generated invoke judgment. -/
namespace Exec.Spec
open SpecExt

/-- Owned typed arguments and the selected signature make the canonical
source invocation configuration semantically typed. -/
theorem invocation_config_ok {s : store} (storeTyped : Store_ok s)
    (address : funcaddr) (params results : List valtype) (args : List val)
    (bound : address < s.FUNCS.length)
    (signature : s.FUNCS[address]!.TYPE = .mk_functype (.mk_list params) (.mk_list results))
    (arguments : ResultsTyped s params args) :
    Config_ok ⟨⟨s,invocationFrame⟩,vals args ++ [.CALL_ADDR address]⟩ (.mk_list results) := by
  have storeWf : wf_store s := by cases storeTyped; assumption
  have typeWf : wf_externtype (.FUNC s.FUNCS[address]!.TYPE) := by constructor
  have external := Externaddr_ok.func s address s.FUNCS[address]! bound rfl storeWf typeWf
  rw [signature] at external typeWf
  have called := Instr_ok2.call_addr s default address params results external storeWf empty_context_wf
    (.admininstr_case_70 _) typeWf
  have callWf : Forall wf_admininstr [.CALL_ADDR address] := by
    simpa [Forall] using wf_admininstr.admininstr_case_70 address
  have valuesWf := wf_vals (resultsTyped_wf arguments)
  have combined := Instrs_ok2.seq s default (vals args) [.CALL_ADDR address] [] results params
    (values_instrs_ok storeWf empty_context_wf arguments)
    (.instr _ _ _ _ _ called storeWf empty_context_wf (.admininstr_case_70 _))
    storeWf empty_context_wf valuesWf callWf
  exact .mk_Config_ok _ _ _ _ default (empty_state_ok s storeTyped)
    (.mk_Expr_ok2 _ _ _ _ combined storeWf empty_context_wf (forall_append valuesWf callWf))
    empty_context_wf (wf_config_make storeWf empty_frame_wf (forall_append valuesWf callWf))
    (.state_case_0 _ _ storeWf empty_frame_wf)

end Exec.Spec
