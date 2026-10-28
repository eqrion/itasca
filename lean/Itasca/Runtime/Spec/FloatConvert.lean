import Itasca.Runtime.Spec.FloatPure
import Itasca.Runtime.Spec.IntegerExtend
namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

/-- Integer conversion uses the concrete rational rounding definition. -/
theorem float_convert_relation (source : Inn) (target : Fnn) (sign : sx) (bits : Nat) :
    fun_cvtop__ (numtype_Inn source) (numtype_Fnn target)
      (.mk_cvtop___1 source target (.CONVERT sign)) (.mk_num__0 source (.mk_uN bits))
      (some [.mk_num__1 target (convert__ (sizenn (numtype_Inn source))
        (sizenn (numtype_Fnn target)) sign (.mk_uN bits))]) := by
  have wf : wf_num_ (numtype_Fnn target) (.mk_num__1 target
      (convert__ (sizenn (numtype_Inn source)) (sizenn (numtype_Fnn target)) sign (.mk_uN bits))) := by
    apply float_num_wf
    unfold convert__
    exact round_wf _ (by cases target <;> decide) _ _
  cases source <;> cases target
  · exact .fun_cvtop___case_16 sign _ wf
  · exact .fun_cvtop___case_18 sign _ wf
  · exact .fun_cvtop___case_17 sign _ wf
  · exact .fun_cvtop___case_19 sign _ wf

/-- The generic generated conversion step, preserving all permitted results. -/
theorem numeric_conversion_pure (source target : numtype) (op : cvtop__) (input result : num_)
    (allowed : List num_) (relation : fun_cvtop__ source target op input (some allowed))
    (chosen : result ∈ allowed) (inputWf : wf_num_ source input)
    (resultWf : wf_num_ target result) (opWf : wf_cvtop__ source target op) (different : target ≠ source) :
    Step_pure [.CONST source input, .CVTOP target source op] [.CONST target result] := by
  apply Step_pure.cvtop_val _ _ _ _ _ _ relation
  · simpa using List.length_pos_of_mem chosen
  · simp
  · simpa using chosen
  · exact wf_admininstr_val (.val_case_0 _ _ inputWf)
  · exact wf_admininstr_instr (.instr_case_18 _ _ _ opWf different)
  · exact wf_admininstr_val (.val_case_0 _ _ resultWf)
end Itasca.Runtime.Spec
namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem float_special_wf (target : Nat) (value : fN)
    (special : isInf value || isZero value) : wf_fN target value := by
  have choice : magnitude value = .INF ∨ magnitude value = .SUBNORM 0 := by
    simpa only [isInf, isZero, Bool.or_eq_true, beq_iff_eq] using special
  cases value <;> simp only [magnitude] at choice
  all_goals rcases choice with rfl | rfl
  all_goals first
    | exact .fN_case_0 _ _ (.fNmag_case_2 _)
    | exact .fN_case_1 _ _ (.fNmag_case_2 _)
    | exact .fN_case_0 _ _ (zero_wf target)
    | exact .fN_case_1 _ _ (zero_wf target)

theorem float_demote_wf (source target : Nat) (width : target = 32 ∨ target = 64)
    (value : fN) : Forall (wf_fN target) (demote__ source target value) := by
  unfold demote__
  split_ifs with hn hc hs
  · exact canonicalNaNs_wf target width
  · exact arithmeticNaNs_wf target width
  · exact singleton_wf (float_special_wf target value hs)
  · exact singleton_wf (round_wf target width _ _)

theorem float_demote_relation (value : fN) :
    fun_cvtop__ .F64 .F32 (.mk_cvtop___3 .F64 .F32 .DEMOTE) (.mk_num__1 .F64 value)
      (some ((demote__ 64 32 value).map (num_.mk_num__1 .F32))) := by
  apply fun_cvtop__.fun_cvtop___case_25
  exact float_results_wf .F32 _ (float_demote_wf 64 32 (by omega) value)

theorem float_convert_pure (source : Inn) (target : Fnn) (sign : sx) (bits : Nat)
    (bound : bits < 2 ^ sizenn (numtype_Inn source)) (result : fN)
    (chosen : result ∈ [convert__ (sizenn (numtype_Inn source)) (sizenn (numtype_Fnn target)) sign (.mk_uN bits)]) :
    Step_pure [.CONST (numtype_Inn source) (.mk_num__0 source (.mk_uN bits)),
      .CVTOP (numtype_Fnn target) (numtype_Inn source) (.mk_cvtop___1 source target (.CONVERT sign))]
      [.CONST (numtype_Fnn target) (.mk_num__1 target result)] := by
  simp only [List.mem_singleton] at chosen
  subst result
  apply numeric_conversion_pure _ _ _ _ _ _ (float_convert_relation source target sign bits)
  · simp
  · exact unsigned_num_wf source bits bound
  · apply float_num_wf
    exact round_wf _ (by cases target <;> decide) _ _
  · exact .cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl
  · cases source <;> cases target <;> decide
end Itasca.Runtime.Spec
