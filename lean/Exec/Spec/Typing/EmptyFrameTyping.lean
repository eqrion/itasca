import Exec.Spec.Typing.ConfigTyping

/-! A canonical typed ambient state for public invocations, which have no
caller-owned Wasm frame. Arbitrary merely well-formed frames need not be typed. -/
namespace Exec.Spec

theorem empty_moduleinst_wf : wf_moduleinst (default : moduleinst) :=
  .moduleinst_case_ [] [] [] [] [] [] [] [] (by simp [Forall])

theorem empty_context_wf : wf_context (default : context) :=
  .context_case_ [] [] [] [] [] [] [] [] [] none (by simp [Forall]) (by simp [Forall])

theorem empty_frame_wf : wf_frame (default : frame) :=
  .frame_case_ [] default (by simp [Forall]) empty_moduleinst_wf

/-- The empty module namespace is typed in every well-formed source store. -/
theorem empty_moduleinst_ok (s : store) (storeWf : wf_store s) :
    Moduleinst_ok s default default := by
  apply Moduleinst_ok.mk_Moduleinst_ok s [] [] [] [] [] [] [] [] [] [] [] [] [] []
  all_goals first | exact storeWf | exact empty_moduleinst_wf | exact empty_context_wf | rfl | simp [Forall,Forall₂,disjoint_,Map]

/-- An empty ambient frame carries the empty source context. -/
theorem empty_frame_ok (s : store) (storeWf : wf_store s) : Frame_ok s default default :=
  .mk_Frame_ok s [] default [] default (empty_moduleinst_ok s storeWf) rfl
    (by simp [Forall₂]) storeWf empty_context_wf empty_frame_wf empty_context_wf

/-- Source store typing suffices to construct a typed canonical ambient state. -/
theorem empty_state_ok (s : store) (typed : Store_ok s) : State_ok ⟨s,default⟩ default := by
  have storeWf : wf_store s := by cases typed; assumption
  exact .mk_State_ok _ _ _ typed (empty_frame_ok s storeWf) empty_context_wf
    (.state_case_0 _ _ storeWf empty_frame_wf)

end Exec.Spec
