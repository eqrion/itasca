import Exec.Abs.Float.Instruction
import Exec.Spec.FloatSigns
import Exec.Spec.FloatMinMax
import Exec.Spec.FloatPromote
import Exec.Spec.FloatComparison
import SpecExt.Builtins.Float.Canonical

namespace Exec.Abs.Float
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

def unaryResults (width : Nat) (op : unop_Fnn) (a : fN) : List fN :=
  match op with
  | .ABS => fabs_ width a | .NEG => fneg_ width a
  | .CEIL => fceil_ width a | .FLOOR => ffloor_ width a
  | .TRUNC => ftrunc_ width a | .NEAREST => fnearest_ width a | .SQRT => fsqrt_ width a

def binaryResults (width : Nat) (op : binop_Fnn) (a b : fN) : List fN :=
  match op with
  | .ADD => fadd_ width a b | .SUB => fsub_ width a b | .MUL => fmul_ width a b
  | .DIV => fdiv_ width a b | .MIN => fmin_ width a b | .MAX => fmax_ width a b
  | .COPYSIGN => fcopysign_ width a b

theorem nans_ne_nil (width : Nat) (validWidth : width = 32 ∨ width = 64) (values : List fN) :
    nans width values ≠ [] := by
  have member := positive_canonical_mem_nans width values (canonical_positive width validWidth)
  intro empty
  simpa only [empty, List.not_mem_nil] using member

theorem unaryResults_ne_nil (width : Nat) (validWidth : width = 32 ∨ width = 64) (op : unop_Fnn) (a : fN) :
    unaryResults width op a ≠ [] := by
  cases op <;> simp only [unaryResults, fabs_, fneg_, fceil_, ffloor_, ftrunc_, fnearest_, integral, fsqrt_]
  all_goals (try split_ifs) <;> simp [nans_ne_nil width validWidth]

theorem binaryResults_ne_nil (width : Nat) (validWidth : width = 32 ∨ width = 64) (op : binop_Fnn) (a b : fN) :
    binaryResults width op a b ≠ [] := by
  cases op <;> simp only [binaryResults, fadd_, fsub_, fmul_, fdiv_, fmin_, fmax_, fcopysign_]
  all_goals (try split_ifs) <;> simp [nans_ne_nil width validWidth]

theorem unaryResults_wf (ty : Fnn) (op : unop_Fnn) (a : fN)
    (first : wf_fN (sizenn (numtype_Fnn ty)) a) : Forall (wf_fN (sizenn (numtype_Fnn ty))) (unaryResults (sizenn (numtype_Fnn ty)) op a) := by
  cases op with
  | ABS => exact Exec.Spec.float_abs_wf _ a first
  | NEG => exact Exec.Spec.float_neg_wf _ a first
  | CEIL => exact integral_wf _ (by cases ty <;> decide) _ a first
  | FLOOR => exact integral_wf _ (by cases ty <;> decide) _ a first
  | TRUNC => exact integral_wf _ (by cases ty <;> decide) _ a first
  | NEAREST => exact integral_wf _ (by cases ty <;> decide) _ a first
  | SQRT => exact sqrt_wf _ (by cases ty <;> decide) a first

theorem unaryResults_relation (ty : Fnn) (op : unop_Fnn) (a : fN)
    (first : wf_fN (sizenn (numtype_Fnn ty)) a) :
    fun_unop_ (numtype_Fnn ty) (.mk_unop__1 ty op) (.mk_num__1 ty a)
      (some ((unaryResults (sizenn (numtype_Fnn ty)) op a).map (num_.mk_num__1 ty))) := by
  cases ty <;> cases op
  all_goals first
    | exact Exec.Spec.float_f32_abs_relation a first
    | exact Exec.Spec.float_f32_neg_relation a first
    | exact Exec.Spec.float_f32_ceil_relation a first
    | exact Exec.Spec.float_f32_floor_relation a first
    | exact Exec.Spec.float_f32_trunc_relation a first
    | exact Exec.Spec.float_f32_nearest_relation a first
    | exact Exec.Spec.float_f32_sqrt_relation a first
    | exact Exec.Spec.float_f64_abs_relation a first
    | exact Exec.Spec.float_f64_neg_relation a first
    | exact Exec.Spec.float_f64_ceil_relation a first
    | exact Exec.Spec.float_f64_floor_relation a first
    | exact Exec.Spec.float_f64_trunc_relation a first
    | exact Exec.Spec.float_f64_nearest_relation a first
    | exact Exec.Spec.float_f64_sqrt_relation a first

theorem binaryResults_wf (ty : Fnn) (op : binop_Fnn) (a b : fN)
    (first : wf_fN (sizenn (numtype_Fnn ty)) a) (second : wf_fN (sizenn (numtype_Fnn ty)) b) : Forall (wf_fN (sizenn (numtype_Fnn ty))) (binaryResults (sizenn (numtype_Fnn ty)) op a b) := by
  cases op with
  | ADD => exact add_wf _ (by cases ty <;> decide) a b first second
  | SUB => exact sub_wf _ (by cases ty <;> decide) a b first second
  | MUL => exact mul_wf _ (by cases ty <;> decide) a b
  | DIV => exact div_wf _ (by cases ty <;> decide) a b
  | MIN => exact Exec.Spec.float_min_wf _ (by cases ty <;> decide) a b first second
  | MAX => exact Exec.Spec.float_max_wf _ (by cases ty <;> decide) a b first second
  | COPYSIGN => exact Exec.Spec.float_copysign_wf _ a b first

theorem binaryResults_relation (ty : Fnn) (op : binop_Fnn) (a b : fN)
    (first : wf_fN (sizenn (numtype_Fnn ty)) a) (second : wf_fN (sizenn (numtype_Fnn ty)) b) :
    fun_binop_ (numtype_Fnn ty) (.mk_binop__1 ty op) (.mk_num__1 ty a) (.mk_num__1 ty b)
      (some ((binaryResults (sizenn (numtype_Fnn ty)) op a b).map (num_.mk_num__1 ty))) := by
  cases ty <;> cases op
  all_goals first
    | exact Exec.Spec.float_f32_add_relation a b first second
    | exact Exec.Spec.float_f32_sub_relation a b first second
    | exact Exec.Spec.float_f32_mul_relation a b first second
    | exact Exec.Spec.float_f32_div_relation a b first second
    | exact Exec.Spec.float_f32_min_relation a b first second
    | exact Exec.Spec.float_f32_max_relation a b first second
    | exact Exec.Spec.float_f32_copysign_relation a b first
    | exact Exec.Spec.float_f64_add_relation a b first second
    | exact Exec.Spec.float_f64_sub_relation a b first second
    | exact Exec.Spec.float_f64_mul_relation a b first second
    | exact Exec.Spec.float_f64_div_relation a b first second
    | exact Exec.Spec.float_f64_min_relation a b first second
    | exact Exec.Spec.float_f64_max_relation a b first second
    | exact Exec.Spec.float_f64_copysign_relation a b first


theorem numberOfBits_float (ty : Fnn) (bits : Nat) :
    numberOfBits (numtype_Fnn ty) bits = .mk_num__1 ty (floatOfBits (sizenn (numtype_Fnn ty)) bits) := by
  cases ty <;> rfl

theorem numberOfBits_integer (ty : Inn) (bits : Nat) :
    numberOfBits (numtype_Inn ty) bits = .mk_num__0 ty (.mk_uN bits) := by
  cases ty <;> rfl

theorem float_encoding (ty : Fnn) (value : fN) (valid : wf_fN (sizenn (numtype_Fnn ty)) value) :
    ∃ bits, bits < 2^sizenn (numtype_Fnn ty) ∧ floatOfBits (sizenn (numtype_Fnn ty)) bits = value := by
  cases ty
  · exact ⟨floatBits 32 value, floatBits_lt_32 value valid, float_roundtrip_32 value valid⟩
  · exact ⟨floatBits 64 value, floatBits_lt_64 value valid, float_roundtrip_64 value valid⟩

theorem unary_result_exists (ty : Fnn) (op : unop_Fnn) (a b : Nat) :
    ∃ bits, (Instruction.unary ty op).Result a b (some bits) := by
  have width : sizenn (numtype_Fnn ty) = 32 ∨ sizenn (numtype_Fnn ty) = 64 := by cases ty <;> decide
  have input := floatOfBits_wf _ width a
  have nonempty := unaryResults_ne_nil _ width op (floatOfBits (sizenn (numtype_Fnn ty)) a)
  obtain ⟨value, chosen⟩ := List.exists_mem_of_ne_nil _ nonempty
  have valid := unaryResults_wf ty op _ input value chosen
  obtain ⟨bits, bound, encoding⟩ := float_encoding ty value valid
  refine ⟨bits, bound, ?_⟩
  have pure := Exec.Spec.float_unary_pure ty op _ value _
    (unaryResults_relation ty op _ input) chosen input valid
  rw [← encoding] at pure
  simpa only [Instruction.operands, Instruction.arity, if_true, Instruction.input,
    Instruction.output, Instruction.source, numberOfBits_float, vals, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, admininstr_val, admininstr_instr] using pure

theorem binary_result_exists (ty : Fnn) (op : binop_Fnn) (a b : Nat) :
    ∃ bits, (Instruction.binary ty op).Result a b (some bits) := by
  have width : sizenn (numtype_Fnn ty) = 32 ∨ sizenn (numtype_Fnn ty) = 64 := by cases ty <;> decide
  have first := floatOfBits_wf _ width a
  have second := floatOfBits_wf _ width b
  have nonempty := binaryResults_ne_nil _ width op (floatOfBits (sizenn (numtype_Fnn ty)) a) (floatOfBits (sizenn (numtype_Fnn ty)) b)
  obtain ⟨value, chosen⟩ := List.exists_mem_of_ne_nil _ nonempty
  have valid := binaryResults_wf ty op _ _ first second value chosen
  obtain ⟨bits, bound, encoding⟩ := float_encoding ty value valid
  refine ⟨bits, bound, ?_⟩
  have pure := Exec.Spec.float_binary_pure ty op _ _ value _
    (binaryResults_relation ty op _ _ first second) chosen first second valid
  rw [← encoding] at pure
  simpa only [Instruction.operands, Instruction.arity, show ¬(2:Nat)=1 from by decide, if_false, Instruction.input,
    Instruction.output, Instruction.source, numberOfBits_float, vals, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, admininstr_val, admininstr_instr] using pure


end Exec.Abs.Float
