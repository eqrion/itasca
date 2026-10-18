import Exec.Spec.Float
namespace Exec.Spec
open SpecExt

/-- A concrete member of a permitted float result list takes one generated step. -/
theorem float_unary_pure (ty : Fnn) (op : unop_Fnn) (a result : fN)
    (allowed : List fN)
    (relation : fun_unop_ (numtype_Fnn ty) (.mk_unop__1 ty op) (.mk_num__1 ty a)
      (some (allowed.map (num_.mk_num__1 ty))))
    (chosen : result ∈ allowed)
    (inputWf : wf_fN (sizenn (numtype_Fnn ty)) a)
    (resultWf : wf_fN (sizenn (numtype_Fnn ty)) result) :
    Step_pure [.CONST (numtype_Fnn ty) (.mk_num__1 ty a),
      .UNOP (numtype_Fnn ty) (.mk_unop__1 ty op)]
      [.CONST (numtype_Fnn ty) (.mk_num__1 ty result)] := by
  apply Step_pure.unop_val _ _ _ _ _ relation
  · simpa using List.length_pos_of_mem chosen
  · simp
  · simp only [Option.get!_some, List.contains_iff_mem]
    exact List.mem_map.mpr ⟨result, chosen, rfl⟩
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty a inputWf))
  · exact wf_admininstr_instr (.instr_case_14 _ _ (.unop__case_1 _ _ _ rfl))
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty result resultWf))

/-- Float binary operators retain the source specification's permitted choices. -/
theorem float_binary_pure (ty : Fnn) (op : binop_Fnn) (a b result : fN)
    (allowed : List fN)
    (relation : fun_binop_ (numtype_Fnn ty) (.mk_binop__1 ty op)
      (.mk_num__1 ty a) (.mk_num__1 ty b) (some (allowed.map (num_.mk_num__1 ty))))
    (chosen : result ∈ allowed)
    (inputWf : wf_fN (sizenn (numtype_Fnn ty)) a)
    (secondWf : wf_fN (sizenn (numtype_Fnn ty)) b)
    (resultWf : wf_fN (sizenn (numtype_Fnn ty)) result) :
    Step_pure [.CONST (numtype_Fnn ty) (.mk_num__1 ty a),
      .CONST (numtype_Fnn ty) (.mk_num__1 ty b),
      .BINOP (numtype_Fnn ty) (.mk_binop__1 ty op)]
      [.CONST (numtype_Fnn ty) (.mk_num__1 ty result)] := by
  apply Step_pure.binop_val _ _ _ _ _ _ relation
  · simpa using List.length_pos_of_mem chosen
  · simp
  · simp only [Option.get!_some, List.contains_iff_mem]
    exact List.mem_map.mpr ⟨result, chosen, rfl⟩
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty a inputWf))
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty b secondWf))
  · exact wf_admininstr_instr (.instr_case_15 _ _ (.binop__case_1 _ _ _ rfl))
  · exact wf_admininstr_val (.val_case_0 _ _ (float_num_wf ty result resultWf))
end Exec.Spec
