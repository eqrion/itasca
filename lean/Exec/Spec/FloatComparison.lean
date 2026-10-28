import Exec.Spec.FloatPure
import Exec.Spec.IntegerDiv
namespace Itasca.Runtime.Spec
open SpecExt

/-- A checked floating comparison reduces to its exact i32 Boolean result. -/
theorem float_comparison_pure (ty : Fnn) (op : relop_Fnn) (a b : fN) (value : Nat)
    (relation : fun_relop_ (numtype_Fnn ty) (.mk_relop__1 ty op)
      (.mk_num__1 ty a) (.mk_num__1 ty b) (some (.mk_num__0 .I32 (.mk_uN value))))
    (ha : wf_fN (sizenn (numtype_Fnn ty)) a) (hb : wf_fN (sizenn (numtype_Fnn ty)) b)
    (bound : value < 2 ^ 32) :
    Step_pure [.CONST (numtype_Fnn ty) (.mk_num__1 ty a),
      .CONST (numtype_Fnn ty) (.mk_num__1 ty b),
      .RELOP (numtype_Fnn ty) (.mk_relop__1 ty op)]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value))] := by
  have wf := unsigned_num_wf .I32 value bound
  apply Step_pure.relop _ _ _ _ _ _ relation
  · simp
  · rfl
  · exact wf
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty a ha))
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty b hb))
  · exact wf_admininstr_instr (.instr_case_17 _ _ (.relop__case_1 _ _ _ rfl))
  · exact wf_admininstr_val (.val_case_0 _ _ wf)

end Itasca.Runtime.Spec
