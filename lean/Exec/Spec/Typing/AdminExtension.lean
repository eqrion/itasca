import Exec.Spec.Typing.FrameExtension

/-! Semantic typing of suspended administrative code survives source store
extension, including callback publication and segment dropping. -/
namespace Exec.Spec

private theorem admin_typing_extension {s t : store} (extension : Extend_store s t) :
    (∀ context instruction type, Instr_ok2 s context instruction type → Instr_ok2 t context instruction type) ∧
    (∀ context instructions type, Instrs_ok2 s context instructions type → Instrs_ok2 t context instructions type) ∧
    (∀ context instructions type, Expr_ok2 s context instructions type → Expr_ok2 t context instructions type) := by
  have fresh := (extend_store_wf extension).2
  refine ⟨?_,?_,?_⟩
  all_goals intro context instructions type typed
  all_goals first
    | induction typed using Instr_ok2.rec
        (motive_2 := fun context instructions type _ => Instrs_ok2 t context instructions type)
        (motive_3 := fun context instructions type _ => Expr_ok2 t context instructions type)
    | induction typed using Instrs_ok2.rec
        (motive_1 := fun context instruction type _ => Instr_ok2 t context instruction type)
        (motive_3 := fun context instructions type _ => Expr_ok2 t context instructions type)
    | induction typed using Expr_ok2.rec
        (motive_1 := fun context instruction type _ => Instr_ok2 t context instruction type)
        (motive_2 := fun context instructions type _ => Instrs_ok2 t context instructions type)
  all_goals first
    | apply Instr_ok2.plain <;> assumption
    | apply Instr_ok2.label <;> assumption
    | apply Instr_ok2.Instr_ok2_frame <;> first
        | assumption
        | exact frame_ok_extend extension (by assumption)
    | apply Instr_ok2.call_addr <;> first
        | assumption
        | exact externaddr_ok_extend extension (by assumption)
    | apply Instr_ok2.ref <;> first
        | assumption
        | exact ref_ok_extend extension (by assumption)
    | apply Instr_ok2.trap <;> assumption
    | apply Instrs_ok2.empty <;> assumption
    | apply Instrs_ok2.instr <;> assumption
    | apply Instrs_ok2.seq <;> assumption
    | apply Instrs_ok2.sub <;> assumption
    | apply Instrs_ok2.Instrs_ok2_frame <;> assumption
    | apply Expr_ok2.mk_Expr_ok2 <;> assumption

theorem instr_ok2_extend {s t : store} (extension : Extend_store s t)
    {context : _root_.context} {instruction : admininstr} {type : functype}
    (typed : Instr_ok2 s context instruction type) : Instr_ok2 t context instruction type :=
  (admin_typing_extension extension).1 _ _ _ typed

theorem instrs_ok2_extend {s t : store} (extension : Extend_store s t)
    {context : _root_.context} {instructions : List admininstr} {type : functype}
    (typed : Instrs_ok2 s context instructions type) : Instrs_ok2 t context instructions type :=
  (admin_typing_extension extension).2.1 _ _ _ typed

theorem expr_ok2_extend {s t : store} (extension : Extend_store s t)
    {context : _root_.context} {instructions : adminexpr} {type : resulttype}
    (typed : Expr_ok2 s context instructions type) : Expr_ok2 t context instructions type :=
  (admin_typing_extension extension).2.2 _ _ _ typed

/-- A callback extension preserves semantic typing of every suspended source
configuration when the returned store is semantically typed. -/
theorem config_ok_extend {s t : store} {frame : _root_.frame} {body : List admininstr} {type : resulttype}
    (extension : Extend_store s t) (storeTyped : Store_ok t)
    (typed : Config_ok ⟨⟨s,frame⟩,body⟩ type) : Config_ok ⟨⟨t,frame⟩,body⟩ type := by
  cases typed with
  | mk_Config_ok _ _ _ types context stateTyped bodyTyped contextWf configWf stateWf =>
    have frameWf := (wf_state_parts stateWf).2
    have bodyWf := (wf_config_parts configWf).2
    exact .mk_Config_ok _ _ _ _ _ (state_ok_extend extension storeTyped stateTyped)
      (expr_ok2_extend extension bodyTyped) contextWf
      (wf_config_make (extend_store_wf extension).2 frameWf bodyWf)
      (.state_case_0 _ _ (extend_store_wf extension).2 frameWf)

end Exec.Spec
