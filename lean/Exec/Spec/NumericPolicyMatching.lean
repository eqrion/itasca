import Exec.Spec.Choices.NumericChoiceCoverage
import Exec.Spec.Choices.Selection
namespace Exec.Spec
open SpecExt SpecExt.Builtins.Float

/-- Pointwise primitive agreement consumes the actual policy at this
occurrence; it assumes no whole interpreter trace or invocation result. -/
theorem chosen_numeric_of_reply {choices : NumericChoices} (occurrence : Nat)
    {request : NumericRequest} {results : List num_} {reply : Option num_}
    (source : request.Allowed results) (same : choices occurrence request results=reply) :
    ChosenNumeric choices occurrence request reply := by
  rw [← same]
  exact .selected results source

theorem chosen_numeric_from_head (occurrence : Nat) {request : NumericRequest}
    {results : List num_} {reply : Option num_} (source : request.Allowed results) (head : results.head?=reply) :
    ChosenNumeric firstNumericChoice occurrence request reply := chosen_numeric_of_reply occurrence source head

theorem chosen_float_binary_first (occurrence : Nat) (type : Fnn) (op : binop_Fnn) (left right value : fN)
    (allowed : List fN) (leftWf : wf_fN (sizenn (numtype_Fnn type)) left)
    (rightWf : wf_fN (sizenn (numtype_Fnn type)) right)
    (source : fun_binop_ (numtype_Fnn type) (.mk_binop__1 type op) (.mk_num__1 type left) (.mk_num__1 type right)
      (some (allowed.map (num_.mk_num__1 type)))) (head : allowed.head?=some value) :
    ChosenNumeric firstNumericChoice occurrence
      (.binary (numtype_Fnn type) (.mk_binop__1 type op) (.mk_num__1 type left) (.mk_num__1 type right))
      (some (.mk_num__1 type value)) := by
  apply chosen_numeric_from_head occurrence
  · apply NumericRequest.Allowed.binary source
    · constructor; exact float_num_wf type _ leftWf
    · constructor; exact float_num_wf type _ rightWf
    · constructor; exact .binop__case_1 _ _ _ rfl
    · exact numeric_binop_results_wf source
  · simp only [List.head?_map,head,Option.map_some]

theorem chosen_float_unary_first (occurrence : Nat) (type : Fnn) (op : unop_Fnn) (input value : fN)
    (allowed : List fN) (inputWf : wf_fN (sizenn (numtype_Fnn type)) input)
    (source : fun_unop_ (numtype_Fnn type) (.mk_unop__1 type op) (.mk_num__1 type input)
      (some (allowed.map (num_.mk_num__1 type)))) (head : allowed.head?=some value) :
    ChosenNumeric firstNumericChoice occurrence
      (.unary (numtype_Fnn type) (.mk_unop__1 type op) (.mk_num__1 type input)) (some (.mk_num__1 type value)) := by
  apply chosen_numeric_from_head occurrence
  · apply NumericRequest.Allowed.unary source
    · constructor; exact float_num_wf type _ inputWf
    · constructor; exact .unop__case_1 _ _ _ rfl
    · exact numeric_unop_results_wf source
  · simp only [List.head?_map,head,Option.map_some]

theorem chosen_vector_of_reply {choices : VectorChoices} (occurrence : Nat)
    {request : VectorRequest} {reply : Option vec_} (source : VectorResultAllowed request reply)
    (same : choices occurrence request=reply) : ChosenVector choices occurrence request reply := by
  rw [← same] at source ⊢
  exact .selected source
end Exec.Spec
