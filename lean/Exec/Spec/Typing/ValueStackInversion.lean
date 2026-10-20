import Exec.Spec.Typing.ValueInversion
import Exec.Spec.Typing.ValueTypingSupport

/-! Inversion of value-only administrative expressions, including subtyping
and stack framing. Terminal configuration typing determines actual results. -/

namespace Exec.Spec
open SpecExt

def ValueTypingEffect (s : store) (values : List val) : functype → Prop
  | .mk_functype (.mk_list input) (.mk_list output) =>
    ∃ base types, Resulttype_sub (.mk_list input) (.mk_list base) ∧ output = base++types ∧ ResultsTyped s types values

set_option maxHeartbeats 1600000 in
theorem values_typing_effect {s : store} {context : _root_.context} {code : List admininstr} {type : functype}
    (typed : Instrs_ok2 s context code type) (values : List val) (same : code = vals values) :
    ValueTypingEffect s values type := by
  refine Instrs_ok2.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ code type _ => ∀ values, code = vals values → ValueTypingEffect s values type)
    (motive_3 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed values same
  all_goals try { intros; trivial }
  case refine_7 =>
    intro context _ _ values same
    have count := congrArg List.length same
    simp only [vals,List.length_map,List.length_nil] at count
    have empty : values = [] := by simpa using count.symm
    subst values
    exact ⟨[],[],resulttype_sub_refl [],rfl,.nil⟩
  case refine_8 =>
    intro context instruction input output primitive _ _ _ _ values same
    have count := congrArg List.length same
    simp only [vals,List.length_map,List.length_cons,List.length_nil] at count
    cases values with
    | nil => simp [vals] at same
    | cons value rest =>
      have lengthZero : rest.length = 0 := by simp only [List.length_cons] at count; omega
      have empty : rest = [] := by simpa using lengthZero
      subst rest
      simp only [vals,List.map_cons,List.map_nil,List.cons.injEq,and_true] at same
      have read : instructionValue instruction = some value := by rw [same]; exact instructionValue_val value
      obtain ⟨rfl,valueType,rfl,valid⟩ := typed_value_instruction primitive read
      exact ⟨[],[valueType],resulttype_sub_refl [],rfl,.cons valid .nil⟩
  case refine_9 =>
    intro context left right input output middle first second _ _ _ _ leftIH rightIH values same
    obtain ⟨xs,ys,valuesEq,leftEq,rightEq⟩ := vals_split same.symm
    obtain ⟨leftBase,leftTypes,leftSub,leftOutput,leftTyped⟩ := leftIH xs leftEq
    obtain ⟨rightBase,rightTypes,rightSub,rightOutput,rightTyped⟩ := rightIH ys rightEq
    rw [leftOutput] at rightSub
    obtain ⟨base,newLeftTypes,baseEq,baseSub,leftTypesSub⟩ := resulttype_sub_append_split rightSub
    refine ⟨base,newLeftTypes++rightTypes,resulttype_sub_trans leftSub baseSub,?_,?_⟩
    · rw [rightOutput,baseEq,List.append_assoc]
    · rw [valuesEq]
      exact resultsTyped_append (resultsTyped_subtype leftTyped leftTypesSub) rightTyped
  case refine_10 =>
    intro context code targetIn targetOut originalIn originalOut original inputSub outputSub _ _ _ ih values same
    obtain ⟨base,types,sub,outputEq,valid⟩ := ih values same
    rw [outputEq] at outputSub
    obtain ⟨newBase,newTypes,newOutput,baseSub,typeSub⟩ := resulttype_sub_append_split outputSub
    exact ⟨newBase,newTypes,resulttype_sub_trans (resulttype_sub_trans inputSub sub) baseSub,
      newOutput,resultsTyped_subtype valid typeSub⟩
  case refine_11 =>
    intro context code frameTypes originalIn originalOut original _ _ _ ih values same
    obtain ⟨base,types,sub,outputEq,valid⟩ := ih values same
    refine ⟨frameTypes++base,types,resulttype_sub_append (resulttype_sub_refl frameTypes) sub,?_,valid⟩
    simp only [outputEq,List.append_assoc]

theorem values_instrs_types {s : store} {context : _root_.context}
    {values : List val} {types : List valtype}
    (typed : Instrs_ok2 s context (vals values) (.mk_functype (.mk_list []) (.mk_list types))) :
    ResultsTyped s types values := by
  obtain ⟨base,actual,sub,output,valid⟩ := values_typing_effect typed values rfl
  have count := (resulttype_sub_iff.mp sub).length_eq
  have empty : base = [] := by simpa using count.symm
  subst base
  simpa only [List.nil_append] using output ▸ valid

theorem values_expr_types {s : store} {context : _root_.context}
    {values : List val} {types : List valtype}
    (typed : Expr_ok2 s context (vals values) (.mk_list types)) : ResultsTyped s types values := by
  cases typed
  apply values_instrs_types
  assumption

theorem values_config_types {s : store} {frame : _root_.frame}
    {values : List val} {types : List valtype}
    (typed : Config_ok ⟨⟨s,frame⟩,vals values⟩ (.mk_list types)) : ResultsTyped s types values := by
  cases typed
  apply values_expr_types
  assumption

end Exec.Spec
