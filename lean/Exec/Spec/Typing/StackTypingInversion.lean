import Exec.Spec.Typing.ValueStackInversion

/-! Stack typing decomposition at arbitrary instruction boundaries and primitive
instruction inversion under subtyping and stack framing. -/

namespace Exec.Spec
open SpecExt

theorem instrs_ok2_wf {s : store} {context : _root_.context} {code : List admininstr} {type : functype}
    (typed : Instrs_ok2 s context code type) :
    wf_store s ∧ wf_context context ∧ Forall wf_admininstr code := by
  cases typed <;> simp_all [Forall]
  aesop

theorem instrs_identity {s : store} {context : _root_.context}
    (storeWf : wf_store s) (contextWf : wf_context context) (types : List valtype) :
    Instrs_ok2 s context [] (.mk_functype (.mk_list types) (.mk_list types)) := by
  simpa using Instrs_ok2.Instrs_ok2_frame s context [] types [] []
    (.empty _ _ storeWf contextWf) storeWf contextWf (by simp [Forall])

theorem instrs_sequence {s : store} {context : _root_.context} {left right : List admininstr}
    {input middle output : List valtype}
    (first : Instrs_ok2 s context left (.mk_functype (.mk_list input) (.mk_list middle)))
    (second : Instrs_ok2 s context right (.mk_functype (.mk_list middle) (.mk_list output))) :
    Instrs_ok2 s context (left++right) (.mk_functype (.mk_list input) (.mk_list output)) := by
  have a := instrs_ok2_wf first
  have b := instrs_ok2_wf second
  exact .seq _ _ _ _ _ _ _ first second a.1 a.2.1 a.2.2 b.2.2

theorem instrs_subtype {s : store} {context : _root_.context} {code : List admininstr}
    {input output targetInput targetOutput : List valtype}
    (typed : Instrs_ok2 s context code (.mk_functype (.mk_list input) (.mk_list output)))
    (inputSub : Resulttype_sub (.mk_list targetInput) (.mk_list input))
    (outputSub : Resulttype_sub (.mk_list output) (.mk_list targetOutput)) :
    Instrs_ok2 s context code (.mk_functype (.mk_list targetInput) (.mk_list targetOutput)) := by
  have wf := instrs_ok2_wf typed
  exact .sub _ _ _ _ _ _ _ typed inputSub outputSub wf.1 wf.2.1 wf.2.2

theorem instrs_frame {s : store} {context : _root_.context} {code : List admininstr}
    {input output : List valtype}
    (typed : Instrs_ok2 s context code (.mk_functype (.mk_list input) (.mk_list output)))
    (base : List valtype) :
    Instrs_ok2 s context code (.mk_functype (.mk_list (base++input)) (.mk_list (base++output))) := by
  have wf := instrs_ok2_wf typed
  exact .Instrs_ok2_frame _ _ _ _ _ _ typed wf.1 wf.2.1 wf.2.2

def TypingSplit (s : store) (context : _root_.context) (left right : List admininstr) : functype → Prop
  | .mk_functype (.mk_list input) (.mk_list output) => ∃ middle : List valtype,
    Instrs_ok2 s context left (.mk_functype (.mk_list input) (.mk_list middle)) ∧
    Instrs_ok2 s context right (.mk_functype (.mk_list middle) (.mk_list output))

set_option maxHeartbeats 1600000 in
theorem instrs_typing_split {s : store} {context : _root_.context} {code : List admininstr} {type : functype}
    (typed : Instrs_ok2 s context code type) (left right : List admininstr) (same : code=left++right) :
    TypingSplit s context left right type := by
  refine Instrs_ok2.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun context code type _ => ∀ left right, code=left++right → TypingSplit s context left right type)
    (motive_3 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed left right same
  all_goals try { intros; trivial }
  case refine_7 =>
    intro context storeWf contextWf left right same
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp same.symm
    exact ⟨[],.empty _ _ storeWf contextWf,.empty _ _ storeWf contextWf⟩
  case refine_8 =>
    intro context instruction input output primitive storeWf contextWf instructionWf _ left right same
    have one := Instrs_ok2.instr _ _ _ _ _ primitive storeWf contextWf instructionWf
    rcases List.append_eq_singleton_iff.mp same.symm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨input,instrs_identity storeWf contextWf input,one⟩
    · exact ⟨output,one,instrs_identity storeWf contextWf output⟩
  case refine_9 =>
    intro context a b input output middle first second _ _ _ _ firstIH secondIH left right same
    rcases List.append_eq_append_iff.mp same with ⟨rest,leftEq,rightEq⟩ | ⟨rest,leftEq,rightEq⟩
    · obtain ⟨between,front,back⟩ := secondIH rest right rightEq
      subst left
      exact ⟨between,instrs_sequence first front,back⟩
    · obtain ⟨between,front,back⟩ := firstIH left rest leftEq
      subst right
      exact ⟨between,front,instrs_sequence back second⟩
  case refine_10 =>
    intro context code targetIn targetOut input output original inputSub outputSub _ _ _ ih left right same
    obtain ⟨middle,first,second⟩ := ih left right same
    exact ⟨middle,instrs_subtype first inputSub (resulttype_sub_refl middle),
      instrs_subtype second (resulttype_sub_refl middle) outputSub⟩
  case refine_11 =>
    intro context code base input output original _ _ _ ih left right same
    obtain ⟨middle,first,second⟩ := ih left right same
    exact ⟨base++middle,instrs_frame first base,instrs_frame second base⟩
theorem value_prefix_typing {s : store} {context : _root_.context}
    {values : List val} {code : List admininstr} {input output : List valtype}
    (typed : Instrs_ok2 s context (vals values++code) (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ base types, Resulttype_sub (.mk_list input) (.mk_list base) ∧ ResultsTyped s types values ∧
      Instrs_ok2 s context code (.mk_functype (.mk_list (base++types)) (.mk_list output)) := by
  obtain ⟨middle,first,second⟩ := instrs_typing_split typed (vals values) code rfl
  obtain ⟨base,types,sub,same,valid⟩ := values_typing_effect first values rfl
  exact ⟨base,types,sub,valid,same ▸ second⟩

theorem closed_value_prefix_typing {s : store} {context : _root_.context}
    {values : List val} {code : List admininstr} {output : List valtype}
    (typed : Instrs_ok2 s context (vals values++code) (.mk_functype (.mk_list []) (.mk_list output))) :
    ∃ types, ResultsTyped s types values ∧
      Instrs_ok2 s context code (.mk_functype (.mk_list types) (.mk_list output)) := by
  obtain ⟨base,types,sub,valid,rest⟩ := value_prefix_typing typed
  have count := (resulttype_sub_iff.mp sub).length_eq
  have empty : base=[] := by simpa using count.symm
  subst base
  exact ⟨types,valid,rest⟩

theorem empty_typing_subtype {s : store} {context : _root_.context} {input output : List valtype}
    (typed : Instrs_ok2 s context [] (.mk_functype (.mk_list input) (.mk_list output))) :
    Resulttype_sub (.mk_list input) (.mk_list output) := by
  obtain ⟨base,types,sub,same,valid⟩ := values_typing_effect typed [] rfl
  have count := valid.length_eq
  have empty : types=[] := by simpa using count.symm
  subst types
  simpa only [same,List.append_nil] using sub

def InstructionTypingEffect (s : store) (context : _root_.context) (instruction : admininstr) : functype → Prop
  | .mk_functype (.mk_list input) (.mk_list output) => ∃ base params results : List valtype,
    Instr_ok2 s context instruction (.mk_functype (.mk_list params) (.mk_list results)) ∧
    Resulttype_sub (.mk_list input) (.mk_list (base++params)) ∧
    Resulttype_sub (.mk_list (base++results)) (.mk_list output)

set_option maxHeartbeats 1600000 in
theorem instruction_typing_effect {s : store} {context : _root_.context} {code : List admininstr} {type : functype}
    (typed : Instrs_ok2 s context code type) (instruction : admininstr) (same : code=[instruction]) :
    InstructionTypingEffect s context instruction type := by
  refine Instrs_ok2.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun context code type _ => ∀ instruction, code=[instruction] → InstructionTypingEffect s context instruction type)
    (motive_3 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed instruction same
  all_goals try { intros; trivial }
  case refine_8 =>
    intro context instruction input output primitive _ _ _ _ chosen same
    have equal : instruction=chosen := by simpa using same
    subst chosen
    exact ⟨[],input,output,primitive,resulttype_sub_refl input,resulttype_sub_refl output⟩
  case refine_9 =>
    intro context a b input output middle first second _ _ _ _ firstIH secondIH instruction same
    rcases List.append_eq_singleton_iff.mp same with ⟨rfl,rightEq⟩ | ⟨leftEq,rfl⟩
    · obtain ⟨base,params,results,primitive,inputSub,outputSub⟩ := secondIH instruction rightEq
      exact ⟨base,params,results,primitive,resulttype_sub_trans (empty_typing_subtype first) inputSub,outputSub⟩
    · obtain ⟨base,params,results,primitive,inputSub,outputSub⟩ := firstIH instruction leftEq
      exact ⟨base,params,results,primitive,inputSub,resulttype_sub_trans outputSub (empty_typing_subtype second)⟩
  case refine_10 =>
    intro context code targetIn targetOut input output original inputSub outputSub _ _ _ ih instruction same
    obtain ⟨base,params,results,primitive,subIn,subOut⟩ := ih instruction same
    exact ⟨base,params,results,primitive,resulttype_sub_trans inputSub subIn,resulttype_sub_trans subOut outputSub⟩
  case refine_11 =>
    intro context code front input output original _ _ _ ih instruction same
    obtain ⟨base,params,results,primitive,subIn,subOut⟩ := ih instruction same
    refine ⟨front++base,params,results,primitive,?_,?_⟩
    · simpa only [List.append_assoc] using resulttype_sub_append (resulttype_sub_refl front) subIn
    · simpa only [List.append_assoc] using resulttype_sub_append (resulttype_sub_refl front) subOut

end Exec.Spec
