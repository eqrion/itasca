import Exec.Spec.Wf
import SpecExt.Builtins.Float.Wf

/-! The concrete arithmetic result lists satisfy the generated numeric rules.
Membership in these lists is the nondeterministic choice consumed by Step. -/
namespace Exec.Spec
open SpecExt SpecExt.Builtins.Float

theorem float_num_wf (ty : Fnn) (value : fN)
    (h : wf_fN (sizenn (numtype_Fnn ty)) value) :
    wf_num_ (numtype_Fnn ty) (.mk_num__1 ty value) :=
  .num__case_1 _ _ _ h rfl

theorem float_results_wf (ty : Fnn) (values : List fN)
    (h : Forall (wf_fN (sizenn (numtype_Fnn ty))) values) :
    Forall (fun value => wf_num_ (numtype_Fnn ty) (.mk_num__1 ty value)) values := by
  intro value hv
  exact float_num_wf ty value (h value hv)

theorem float_f32_add_relation (a b : fN)
    (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .ADD) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fadd_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_24
  · exact add_wf 32 (by omega) a b ha hb
  · exact float_results_wf .F32 _ (add_wf 32 (by omega) a b ha hb)

theorem float_f32_sub_relation (a b : fN)
    (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .SUB) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fsub_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_26
  · exact sub_wf 32 (by omega) a b ha hb
  · exact float_results_wf .F32 _ (sub_wf 32 (by omega) a b ha hb)

theorem float_f32_mul_relation (a b : fN)
    (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .MUL) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fmul_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_28
  · exact mul_wf 32 (by omega) a b
  · exact float_results_wf .F32 _ (mul_wf 32 (by omega) a b)

theorem float_f32_div_relation (a b : fN)
    (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .DIV) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fdiv_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_30
  · exact div_wf 32 (by omega) a b
  · exact float_results_wf .F32 _ (div_wf 32 (by omega) a b)

theorem float_f32_sqrt_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .SQRT) (.mk_num__1 .F32 a)
      (some ((fsqrt_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_12
  exact float_results_wf .F32 _ (sqrt_wf 32 (by omega) a ha)

theorem float_f32_ceil_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .CEIL) (.mk_num__1 .F32 a)
      (some ((fceil_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_14
  exact float_results_wf .F32 _ (integral_wf 32 (by omega) _ a ha)

theorem float_f32_floor_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .FLOOR) (.mk_num__1 .F32 a)
      (some ((ffloor_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_16
  exact float_results_wf .F32 _ (integral_wf 32 (by omega) _ a ha)

theorem float_f32_trunc_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .TRUNC) (.mk_num__1 .F32 a)
      (some ((ftrunc_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_18
  exact float_results_wf .F32 _ (integral_wf 32 (by omega) _ a ha)

theorem float_f32_nearest_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEAREST) (.mk_num__1 .F32 a)
      (some ((fnearest_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_20
  exact float_results_wf .F32 _ (integral_wf 32 (by omega) _ a ha)

theorem float_f64_add_relation (a b : fN)
    (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .ADD) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fadd_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_25
  · exact add_wf 64 (by omega) a b ha hb
  · exact float_results_wf .F64 _ (add_wf 64 (by omega) a b ha hb)

theorem float_f64_sub_relation (a b : fN)
    (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .SUB) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fsub_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_27
  · exact sub_wf 64 (by omega) a b ha hb
  · exact float_results_wf .F64 _ (sub_wf 64 (by omega) a b ha hb)

theorem float_f64_mul_relation (a b : fN)
    (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .MUL) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fmul_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_29
  · exact mul_wf 64 (by omega) a b
  · exact float_results_wf .F64 _ (mul_wf 64 (by omega) a b)

theorem float_f64_div_relation (a b : fN)
    (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .DIV) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fdiv_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_31
  · exact div_wf 64 (by omega) a b
  · exact float_results_wf .F64 _ (div_wf 64 (by omega) a b)

theorem float_f64_sqrt_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .SQRT) (.mk_num__1 .F64 a)
      (some ((fsqrt_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_13
  exact float_results_wf .F64 _ (sqrt_wf 64 (by omega) a ha)

theorem float_f64_ceil_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .CEIL) (.mk_num__1 .F64 a)
      (some ((fceil_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_15
  exact float_results_wf .F64 _ (integral_wf 64 (by omega) _ a ha)

theorem float_f64_floor_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .FLOOR) (.mk_num__1 .F64 a)
      (some ((ffloor_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_17
  exact float_results_wf .F64 _ (integral_wf 64 (by omega) _ a ha)

theorem float_f64_trunc_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .TRUNC) (.mk_num__1 .F64 a)
      (some ((ftrunc_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_19
  exact float_results_wf .F64 _ (integral_wf 64 (by omega) _ a ha)

theorem float_f64_nearest_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEAREST) (.mk_num__1 .F64 a)
      (some ((fnearest_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_21
  exact float_results_wf .F64 _ (integral_wf 64 (by omega) _ a ha)

end Exec.Spec
