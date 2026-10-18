import Exec.Abs.Float.Results
import Exec.Spec.FloatReinterpret
namespace Exec.Abs.Float
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem numberOfBits_i32 (bits : Nat) : numberOfBits .I32 bits = .mk_num__0 .I32 (.mk_uN bits) := rfl

def compareNumber (width : Nat) (op : relop_Fnn) (a b : fN) : iN :=
  match op with
  | .EQ => feq_ width a b | .NE => fne_ width a b | .LT => flt_ width a b
  | .GT => fgt_ width a b | .LE => fle_ width a b | .GE => fge_ width a b

theorem compareNumber_bound (width : Nat) (op : relop_Fnn) (a b : fN) :
    proj_uN_0 (compareNumber width op a b) < 2^32 := by
  cases op <;> simp only [compareNumber, feq_, fne_, flt_, fgt_, fle_, fge_]
  all_goals split <;> decide

theorem compareNumber_relation (ty : Fnn) (op : relop_Fnn) (a b : fN) :
    fun_relop_ (numtype_Fnn ty) (.mk_relop__1 ty op) (.mk_num__1 ty a) (.mk_num__1 ty b)
      (some (.mk_num__0 .I32 (.mk_uN (proj_uN_0 (compareNumber (sizenn (numtype_Fnn ty)) op a b))))) := by
  have valid := Exec.Spec.unsigned_num_wf .I32 _ (compareNumber_bound (sizenn (numtype_Fnn ty)) op a b)
  have same : uN.mk_uN (proj_uN_0 (compareNumber (sizenn (numtype_Fnn ty)) op a b)) =
      compareNumber (sizenn (numtype_Fnn ty)) op a b := by cases compareNumber (sizenn (numtype_Fnn ty)) op a b <;> rfl
  rw [same] at valid ⊢
  cases ty <;> cases op
  all_goals first
    | exact .fun_relop__case_12 _ _ valid
    | exact .fun_relop__case_13 _ _ valid
    | exact .fun_relop__case_14 _ _ valid
    | exact .fun_relop__case_15 _ _ valid
    | exact .fun_relop__case_16 _ _ valid
    | exact .fun_relop__case_17 _ _ valid
    | exact .fun_relop__case_18 _ _ valid
    | exact .fun_relop__case_19 _ _ valid
    | exact .fun_relop__case_20 _ _ valid
    | exact .fun_relop__case_21 _ _ valid
    | exact .fun_relop__case_22 _ _ valid
    | exact .fun_relop__case_23 _ _ valid

theorem compare_result_exists (ty : Fnn) (op : relop_Fnn) (a b : Nat) :
    ∃ bits, (Instruction.compare ty op).Result a b (some bits) := by
  have width : sizenn (numtype_Fnn ty) = 32 ∨ sizenn (numtype_Fnn ty) = 64 := by cases ty <;> decide
  have first := floatOfBits_wf _ width a
  have second := floatOfBits_wf _ width b
  have bound := compareNumber_bound (sizenn (numtype_Fnn ty)) op
    (floatOfBits (sizenn (numtype_Fnn ty)) a) (floatOfBits (sizenn (numtype_Fnn ty)) b)
  refine ⟨_, bound, ?_⟩
  have pure := Exec.Spec.float_comparison_pure ty op _ _ _ (compareNumber_relation ty op _ _) first second bound
  simpa only [Instruction.operands, Instruction.arity, show ¬(2:Nat)=1 from by decide, if_false, Instruction.input,
    Instruction.output, Instruction.source, numberOfBits_float, numberOfBits_i32, vals, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, admininstr_val, admininstr_instr] using pure

theorem convert_result_exists (source : Inn) (target : Fnn) (sign : sx) (a b : Nat)
    (inputBound : a < 2^sizenn (numtype_Inn source)) :
    ∃ bits, (Instruction.convert source target sign).Result a b (some bits) := by
  let value := convert__ (sizenn (numtype_Inn source)) (sizenn (numtype_Fnn target)) sign (.mk_uN a)
  have valid : wf_fN (sizenn (numtype_Fnn target)) value := by
    unfold value convert__
    exact round_wf _ (by cases target <;> decide) _ _
  obtain ⟨bits, bound, encoding⟩ := float_encoding target value valid
  refine ⟨bits, bound, ?_⟩
  have pure := Exec.Spec.float_convert_pure source target sign a inputBound value (by simp [value])
  rw [← encoding] at pure
  simpa only [Instruction.operands, Instruction.arity, if_true, Instruction.input,
    Instruction.output, Instruction.source, numberOfBits_float, numberOfBits_integer, vals, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, admininstr_val, admininstr_instr] using pure

theorem integer_number_bound (target : Inn) (bits : Nat)
    (valid : wf_num_ (numtype_Inn target) (.mk_num__0 target (.mk_uN bits))) :
    bits < 2^sizenn (numtype_Inn target) := by
  cases valid with
  | num__case_0 _ _ sizePresent bounded same =>
    cases bounded with
    | uN_case_0 _ limit =>
      cases target <;> norm_num [sizenn, numtype_Inn, valtype_numtype, valtype_Inn, size] at limit ⊢ <;> omega

theorem truncate_result_exists (source : Fnn) (target : Inn) (sign : sx) (sat : Bool) (a b : Nat) :
    ∃ result, (Instruction.truncate source target sign sat).Result a b result := by
  let value := floatOfBits (sizenn (numtype_Fnn source)) a
  let expected := if sat then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value
    else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign value
  have valid := floatOfBits_wf (sizenn (numtype_Fnn source)) (by cases source <;> decide) a
  have resultsWf : Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result)) expected.toList := by
    cases sat
    · exact Exec.Spec.float_trunc_results_wf _ target sign value
    · exact Exec.Spec.float_trunc_sat_results_wf _ target sign value
  cases outcome : expected with
  | none =>
    refine ⟨none, ?_⟩
    have pure := Exec.Spec.float_truncation_pure source target sign sat value none outcome valid
    simpa only [Instruction.Result, Instruction.operands, Instruction.arity, if_true, Instruction.input,
      Instruction.output, Instruction.source, numberOfBits_float, numberOfBits_i32, vals, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, admininstr_val, admininstr_instr, value] using pure
  | some result =>
    cases result with
    | mk_uN bits =>
      have numberWf := resultsWf (.mk_uN bits) (by simp [outcome])
      refine ⟨some bits, integer_number_bound target bits numberWf, ?_⟩
      have pure := Exec.Spec.float_truncation_pure source target sign sat value (some (.mk_uN bits)) outcome valid
      simpa only [Instruction.operands, Instruction.arity, if_true, Instruction.input,
        Instruction.output, Instruction.source, numberOfBits_float, numberOfBits_integer, vals, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, admininstr_val, admininstr_instr, value] using pure

theorem reinterpret_float_result_exists (source : Fnn) (a b : Nat)
    (bound : a < 2^sizenn (numtype_Fnn source)) :
    ∃ bits, (Instruction.reinterpretFloat source).Result a b (some bits) := by
  cases source
  · exact ⟨a, bound, Exec.Spec.i32_reinterpret_f32_pure a bound⟩
  · exact ⟨a, bound, Exec.Spec.i64_reinterpret_f64_pure a bound⟩

theorem reinterpret_integer_result_exists (source : Inn) (a b : Nat)
    (bound : a < 2^sizenn (numtype_Inn source)) :
    ∃ bits, (Instruction.reinterpretInt source).Result a b (some bits) := by
  cases source
  · exact ⟨a, bound, Exec.Spec.f32_reinterpret_i32_pure a bound⟩
  · exact ⟨a, bound, Exec.Spec.f64_reinterpret_i64_pure a bound⟩

theorem demote_ne_nil (source target : Nat) (validWidth : target = 32 ∨ target = 64) (value : fN) :
    demote__ source target value ≠ [] := by
  unfold demote__
  split_ifs
  · intro empty
    have member := positive_canonical_mem target
    simpa only [empty, List.not_mem_nil] using member
  · intro empty
    have member := positive_canonical_mem_arithmetic target (canonical_positive target validWidth)
    simpa only [empty, List.not_mem_nil] using member
  · simp
  · simp

theorem promote_result_exists (a b : Nat) :
    ∃ bits, Instruction.promote.Result a b (some bits) := by
  have nonempty := demote_ne_nil 32 64 (by decide) (floatOfBits 32 a)
  obtain ⟨value, chosen⟩ := List.exists_mem_of_ne_nil _ nonempty
  have valid := Exec.Spec.float_demote_wf 32 64 (by decide) (floatOfBits 32 a) value chosen
  obtain ⟨bits, bound, encoding⟩ := float_encoding .F64 value valid
  refine ⟨bits, bound, ?_⟩
  have pure := Exec.Spec.numeric_conversion_pure .F32 .F64 (.mk_cvtop___3 .F32 .F64 .PROMOTE)
    (.mk_num__1 .F32 (floatOfBits 32 a)) (.mk_num__1 .F64 value) _ (Exec.Spec.float_promote_relation _)
    (List.mem_map.mpr ⟨value, chosen, rfl⟩)
    (Exec.Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by decide) _))
    (Exec.Spec.float_num_wf .F64 value valid)
    (.cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_0 _ _ (by decide)) rfl rfl) (by decide)
  rw [← encoding] at pure
  exact pure

theorem demote_result_exists (a b : Nat) :
    ∃ bits, Instruction.demote.Result a b (some bits) := by
  have nonempty := demote_ne_nil 64 32 (by decide) (floatOfBits 64 a)
  obtain ⟨value, chosen⟩ := List.exists_mem_of_ne_nil _ nonempty
  have valid := Exec.Spec.float_demote_wf 64 32 (by decide) (floatOfBits 64 a) value chosen
  obtain ⟨bits, bound, encoding⟩ := float_encoding .F32 value valid
  refine ⟨bits, bound, ?_⟩
  have pure := Exec.Spec.numeric_conversion_pure .F64 .F32 (.mk_cvtop___3 .F64 .F32 .DEMOTE)
    (.mk_num__1 .F64 (floatOfBits 64 a)) (.mk_num__1 .F32 value) _ (Exec.Spec.float_demote_relation _)
    (List.mem_map.mpr ⟨value, chosen, rfl⟩)
    (Exec.Spec.float_num_wf .F64 _ (floatOfBits_wf 64 (by decide) _))
    (Exec.Spec.float_num_wf .F32 value valid)
    (.cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl) (by decide)
  rw [← encoding] at pure
  exact pure

theorem Instruction.progress (op : Instruction) (a b : Nat)
    (first : a < 2^sizenn op.input) : ∃ result, op.Result a b result := by
  cases op with
  | unary ty operation => obtain ⟨bits, effect⟩ := unary_result_exists ty operation a b; exact ⟨some bits, effect⟩
  | binary ty operation => obtain ⟨bits, effect⟩ := binary_result_exists ty operation a b; exact ⟨some bits, effect⟩
  | compare ty operation => obtain ⟨bits, effect⟩ := compare_result_exists ty operation a b; exact ⟨some bits, effect⟩
  | convert source target sign => obtain ⟨bits, effect⟩ := convert_result_exists source target sign a b first; exact ⟨some bits, effect⟩
  | truncate source target sign sat => exact truncate_result_exists source target sign sat a b
  | reinterpretFloat source => obtain ⟨bits, effect⟩ := reinterpret_float_result_exists source a b first; exact ⟨some bits, effect⟩
  | reinterpretInt source => obtain ⟨bits, effect⟩ := reinterpret_integer_result_exists source a b first; exact ⟨some bits, effect⟩
  | promote => obtain ⟨bits, effect⟩ := promote_result_exists a b; exact ⟨some bits, effect⟩
  | demote => obtain ⟨bits, effect⟩ := demote_result_exists a b; exact ⟨some bits, effect⟩

end Exec.Abs.Float
