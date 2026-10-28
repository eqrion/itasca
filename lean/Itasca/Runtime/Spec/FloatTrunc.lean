import Itasca.Runtime.Spec.FloatConvert
namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem encodeSigned_num_wf (target : Inn) (value : Int) :
    wf_num_ (numtype_Inn target) (.mk_num__0 target (encodeSigned (sizenn (numtype_Inn target)) value)) := by
  have bound := (BitVec.ofInt (sizenn (numtype_Inn target)) value).isLt
  apply unsigned_num_wf
  simpa [encodeSigned, BitVec.toNat_ofInt] using bound

theorem saturate_num_wf (target : Inn) (sign : sx) (value : Int) :
    wf_num_ (numtype_Inn target) (.mk_num__0 target (saturate (sizenn (numtype_Inn target)) sign value)) := by
  cases sign with
  | S =>
    unfold saturate
    exact encodeSigned_num_wf target _
  | U =>
    unfold saturate
    apply unsigned_num_wf
    have positive : (0:Int) < 2^(sizenn (numtype_Inn target)) := by positivity
    have upper : max 0 (min value ((2:Int)^(sizenn (numtype_Inn target))-1)) < 2^(sizenn (numtype_Inn target)) := by omega
    have nonnegative : (0:Int) ≤ max 0 (min value ((2:Int)^(sizenn (numtype_Inn target))-1)) := by omega
    rw [Int.toNat_lt nonnegative]
    exact_mod_cast upper

theorem float_trunc_results_wf (source : Nat) (target : Inn) (sign : sx) (value : fN) :
    Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result))
      (trunc__ source (sizenn (numtype_Inn target)) sign value).toList := by
  unfold trunc__
  split
  · simp [Forall]
  · split <;> simp [Forall, encodeSigned_num_wf]

theorem float_trunc_sat_results_wf (source : Nat) (target : Inn) (sign : sx) (value : fN) :
    Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result))
      (trunc_sat__ source (sizenn (numtype_Inn target)) sign value).toList := by
  unfold trunc_sat__
  split
  · simp only [Option.toList_some, Forall, List.mem_singleton, forall_eq]
    exact unsigned_num_wf target 0 (by positivity)
  · split <;> simp [Forall, saturate_num_wf]

theorem option_list_map (f : α → β) (value : Option α) :
    list_ β (OMap f value) = value.toList.map f := by cases value <;> rfl

theorem float_trunc_relation (source : Fnn) (target : Inn) (sign : sx) (value : fN) :
    fun_cvtop__ (numtype_Fnn source) (numtype_Inn target)
      (.mk_cvtop___2 source target (.TRUNC sign)) (.mk_num__1 source value)
      (some ((trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value).toList.map (num_.mk_num__0 target))) := by
  have wf := float_trunc_results_wf (sizenn (numtype_Fnn source)) target sign value
  cases source <;> cases target
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_8 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_10 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_9 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_11 sign value wf

theorem float_trunc_sat_relation (source : Fnn) (target : Inn) (sign : sx) (value : fN) :
    fun_cvtop__ (numtype_Fnn source) (numtype_Inn target)
      (.mk_cvtop___2 source target (.TRUNC_SAT sign)) (.mk_num__1 source value)
      (some ((trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value).toList.map (num_.mk_num__0 target))) := by
  have wf := float_trunc_sat_results_wf (sizenn (numtype_Fnn source)) target sign value
  cases source <;> cases target
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_12 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_14 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_13 sign value wf
  · simpa only [option_list_map, sizenn, sizenn1, sizenn2, numtype_Inn, numtype_Fnn, valtype_numtype, size, Option.get!] using fun_cvtop__.fun_cvtop___case_15 sign value wf

theorem float_truncation_pure (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
    (value : fN) (expected : Option iN)
    (conversion : (if saturating then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value) = expected)
    (inputWf : wf_fN (sizenn (numtype_Fnn source)) value) :
    Step_pure [.CONST (numtype_Fnn source) (.mk_num__1 source value),
      .CVTOP (numtype_Inn target) (numtype_Fnn source)
        (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))]
      (match expected with
       | some result => [.CONST (numtype_Inn target) (.mk_num__0 target result)]
       | none => [.TRAP]) := by
  have relation : fun_cvtop__ (numtype_Fnn source) (numtype_Inn target)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))
      (.mk_num__1 source value) (some (expected.toList.map (num_.mk_num__0 target))) := by
    rw [← conversion]
    cases saturating
    · exact float_trunc_relation source target sign value
    · exact float_trunc_sat_relation source target sign value
  have resultsWf : Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result)) expected.toList := by
    rw [← conversion]
    cases saturating
    · exact float_trunc_results_wf _ target sign value
    · exact float_trunc_sat_results_wf _ target sign value
  have opWf : wf_cvtop__ (numtype_Fnn source) (numtype_Inn target)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign)) := by
    apply wf_cvtop__.cvtop___case_2
    · cases saturating
      · exact .cvtop__Fnn_1_Inn_2_case_0 _ _ _
      · exact .cvtop__Fnn_1_Inn_2_case_1 _ _ _
    · rfl
    · rfl
  have input : wf_num_ (numtype_Fnn source) (.mk_num__1 source value) := float_num_wf source value inputWf
  have different : numtype_Inn target ≠ numtype_Fnn source := by cases source <;> cases target <;> decide
  cases expected with
  | none =>
    apply Step_pure.cvtop_trap _ _ _ _ _ relation
    · simp
    · rfl
    · exact wf_admininstr_val (.val_case_0 _ _ input)
    · exact wf_admininstr_instr (.instr_case_18 _ _ _ opWf different)
    · exact .admininstr_case_73
  | some result =>
    apply numeric_conversion_pure _ _ _ _ _ _ relation
    · simp
    · exact input
    · exact resultsWf result (by simp)
    · exact opWf
    · exact different
end Itasca.Runtime.Spec
