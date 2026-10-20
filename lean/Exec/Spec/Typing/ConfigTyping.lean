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

/-- A trap has every result type in a typed source state. In particular, a
trap does not discard the semantic typing of its retained store and frame. -/
theorem trap_config_ok {s : store} {f : frame} {context : _root_.context}
    (typed : State_ok ⟨s,f⟩ context) (types : List valtype) :
    Config_ok ⟨⟨s,f⟩,[.TRAP]⟩ (.mk_list types) := by
  have stateWf : wf_state ⟨s,f⟩ := by cases typed; assumption
  have storeWf : wf_store s := by cases stateWf; assumption
  have frameWf : wf_frame f := by cases stateWf; assumption
  have contextWf : wf_context context := by cases typed; assumption
  have trapWf : wf_admininstr .TRAP := .admininstr_case_73
  apply Config_ok.mk_Config_ok _ _ _ _ context typed
  · apply Expr_ok2.mk_Expr_ok2
    · exact Instrs_ok2.instr _ _ _ _ _
        (Instr_ok2.trap _ _ [] types storeWf contextWf trapWf) storeWf contextWf trapWf
    · exact storeWf
    · exact contextWf
    · simpa [Forall] using trapWf
  · exact contextWf
  · exact wf_config_make storeWf frameWf (by simpa [Forall] using trapWf)
  · exact stateWf

/-- Any rule retaining the state and producing a trap preserves configuration
typing. This applies independently of the particular trap cause. -/
theorem config_ok_trap {s : store} {f : frame} {body : List admininstr} {types : resulttype}
    (typed : Config_ok ⟨⟨s,f⟩,body⟩ types) : Config_ok ⟨⟨s,f⟩,[.TRAP]⟩ types := by
  cases typed with
  | mk_Config_ok _ _ _ results context state _ _ _ _ => exact trap_config_ok state results

end Exec.Spec
