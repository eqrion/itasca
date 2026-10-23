import Exec.Spec.Wf

/-! Source configuration typing projections and trap typing. These lemmas use
semantic typing, rather than only the generated well-formedness predicates. -/
namespace Exec.Spec

/-- A typed source state contains a store satisfying generated store typing. -/
theorem state_ok_store {s : store} {f : frame} {context : _root_.context}
    (typed : State_ok ⟨s,f⟩ context) : Store_ok s := by
  cases typed
  assumption

/-- A configuration's semantic typing includes its source store typing. -/
theorem config_ok_store {s : store} {f : frame} {body : List admininstr} {types : resulttype}
    (typed : Config_ok ⟨⟨s,f⟩,body⟩ types) : Store_ok s := by
  cases typed
  apply state_ok_store
  assumption

end Exec.Spec
