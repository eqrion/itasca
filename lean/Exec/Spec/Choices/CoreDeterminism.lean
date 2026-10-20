import Exec.Spec.Choices.RedexFamily
import Exec.Spec.Choices.RedexDecomposition
import Exec.Spec.Choices.InputUniqueness
import Exec.Spec.HostReadDisjoint
import Exec.Spec.Choices.ReadDeterminism
import Exec.Spec.Choices.ControlTerminal
namespace Exec.Spec
open SpecExt

private theorem residualCode_ref (value : ref) (tail : List admininstr) :
    residualCode (admininstr_ref value::tail)=residualCode tail := by cases value <;> rfl

private def labelWrap (arity : Nat) (cont : List instr) : config → config
  | ⟨z,body⟩ => ⟨z,[.LABEL_ arity cont body]⟩

private def frameWrap (arity : Nat) (ambient : frame) : config → config
  | ⟨⟨s,f⟩,body⟩ => ⟨⟨s,ambient⟩,[.FRAME_ arity f body]⟩

private theorem label_children_equal {choices : SourceChoices} {occurrence limit arity : Nat} {cont : List instr}
    {z leftState rightState : state} {body leftBody rightBody : List admininstr} {le re : List HostEvent}
    (children : ∀ state body leftEvents rightEvents left right,
      sizeOf body<limit → activeTrap body=false →
      ChoiceStep choices occurrence ⟨state,body⟩ leftEvents left →
      ChoiceStep choices occurrence ⟨state,body⟩ rightEvents right → leftEvents=rightEvents ∧ left=right)
    (bounded : sizeOf [admininstr.LABEL_ arity cont body]≤limit) (nonactive : activeTrap [.LABEL_ arity cont body]=false)
    (first : ChoiceStep choices occurrence ⟨z,body⟩ le ⟨leftState,leftBody⟩)
    (second : ChoiceStep choices occurrence ⟨z,body⟩ re ⟨rightState,rightBody⟩) :
    le=re ∧ config.mk_config leftState [.LABEL_ arity cont leftBody]=⟨rightState,[.LABEL_ arity cont rightBody]⟩ := by
  have small : sizeOf body<sizeOf [admininstr.LABEL_ arity cont body] := by
    simp only [List.cons.sizeOf_spec,List.nil.sizeOf_spec,admininstr.LABEL_.sizeOf_spec]
    omega
  have active : activeTrap body=false := by simpa only [activeTrap] using nonactive
  obtain ⟨eventsEq,afterEq⟩ := children z body le re _ _ (by omega) active first second
  exact ⟨eventsEq,congrArg (labelWrap arity cont) afterEq⟩

private theorem frame_children_equal {choices : SourceChoices} {occurrence limit arity : Nat}
    {s leftStore rightStore : store} {ambient inner leftFrame rightFrame : frame}
    {body leftBody rightBody : List admininstr} {le re : List HostEvent}
    (children : ∀ state body leftEvents rightEvents left right,
      sizeOf body<limit → activeTrap body=false →
      ChoiceStep choices occurrence ⟨state,body⟩ leftEvents left →
      ChoiceStep choices occurrence ⟨state,body⟩ rightEvents right → leftEvents=rightEvents ∧ left=right)
    (bounded : sizeOf [admininstr.FRAME_ arity inner body]≤limit) (nonactive : activeTrap [.FRAME_ arity inner body]=false)
    (first : ChoiceStep choices occurrence ⟨⟨s,inner⟩,body⟩ le ⟨⟨leftStore,leftFrame⟩,leftBody⟩)
    (second : ChoiceStep choices occurrence ⟨⟨s,inner⟩,body⟩ re ⟨⟨rightStore,rightFrame⟩,rightBody⟩) :
    le=re ∧ config.mk_config ⟨leftStore,ambient⟩ [.FRAME_ arity leftFrame leftBody]=
      ⟨⟨rightStore,ambient⟩,[.FRAME_ arity rightFrame rightBody]⟩ := by
  have small : sizeOf body<sizeOf [admininstr.FRAME_ arity inner body] := by
    simp only [List.cons.sizeOf_spec,List.nil.sizeOf_spec,admininstr.FRAME_.sizeOf_spec]
    omega
  have active : activeTrap body=false := by simpa only [activeTrap] using nonactive
  obtain ⟨eventsEq,afterEq⟩ := children ⟨s,inner⟩ body le re _ _ (by omega) active first second
  exact ⟨eventsEq,congrArg (frameWrap arity ambient) afterEq⟩

set_option maxHeartbeats 4000000 in
theorem core_deterministic_of_children {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence limit : Nat} {before other left right : config} {leftEvents rightEvents : List HostEvent}
    (first : CoreChoiceStep choices occurrence before leftEvents left)
    (second : CoreChoiceStep choices occurrence other rightEvents right) (same : before=other)
    (nonactive : activeTrap (trapCode before)=false)
    (bounded : sizeOf (trapCode before)≤limit)
    (children : ∀ state body leftEvents rightEvents left right,
      sizeOf body<limit → activeTrap body=false →
      ChoiceStep choices occurrence ⟨state,body⟩ leftEvents left →
      ChoiceStep choices occurrence ⟨state,body⟩ rightEvents right → leftEvents=rightEvents ∧ left=right) :
    leftEvents=rightEvents ∧ left=right := by
  have otherNonactive : activeTrap (trapCode other)=false := by rw [← same]; exact nonactive
  have family := congrArg (fun c => codeRedexFamily (trapCode c)) same
  cases first
  all_goals cases second
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try (with_reducible exact ⟨rfl,rfl⟩)
  all_goals try (with_reducible contradiction)
  all_goals try dsimp only [trapCode] at *
  all_goals try have pureFamily := pure_redex_family (by assumption) (by first | assumption | rfl) (by first | assumption | simp [activeTrap])
  all_goals try have readFamily := read_redex_family (by assumption)
  all_goals try have writeFamily := DirectWrite.redex_family (by assumption)
  all_goals try dsimp only [trapCode] at *
  all_goals try have numericFamily := NumericRequest.redex_family (by assumption)
  all_goals try have vectorFamily := VectorRequest.redex_family (by assumption)
  all_goals try simp only [codeRedexFamily,residualCode_vals,residualCode_value,residualCode_ref,residualCode,
    redexFamily,Segment.i32,List.head!_cons] at *
  all_goals try omega
  all_goals try (with_reducible grind only [NumericRequest.redex_family,VectorRequest.redex_family])

  case ordinary_pure.ordinary_pure =>
    constructor
    · trivial
    · apply congrArg (fun code => config.mk_config _ code)
      exact choice_free_pure_nonactive_deterministic (by assumption) (by assumption) (by assumption) (by assumption)
  case ordinary_read.ordinary_read =>
    constructor
    · trivial
    · apply congrArg (fun code => config.mk_config _ code)
      exact read_same_input_deterministic (by assumption) (by assumption)
  case write.write =>
    constructor
    · trivial
    · exact DirectWrite.deterministic (by assumption) (by assumption) rfl
  case numeric.numeric =>
    have requestSame := NumericRequest.instructions_injective (by assumption)
    cases requestSame
    with_reducible grind only [ChosenNumeric.deterministic]
  case vector.vector =>
    have requestSame := VectorRequest.instructions_injective (by assumption)
    cases requestSame
    with_reducible grind only [ChosenVector.deterministic]
  case table.table => with_reducible grind only [ref_instruction_injective]
  case ordinary_read.host | host.ordinary_read =>
    exfalso
    exact read_not_host_call (by assumption) (by assumption) rfl
  case ordinary_pure.label | label.ordinary_pure =>
    exfalso
    apply (pure_label_body_terminal (by assumption) rfl _ _ _)
    exact ChoiceStep.erases admissible (by assumption)
  case ordinary_pure.frame | frame.ordinary_pure =>
    exfalso
    apply (pure_frame_body_terminal (by assumption) rfl _ _ _)
    exact ChoiceStep.erases admissible (by assumption)
  case host.host =>
    have parts := value_prefix_unique (first := .CALL_ADDR _) (second := .CALL_ADDR _) rfl rfl (by assumption)
    obtain ⟨argsEq,opEq,_⟩ := parts
    cases argsEq
    cases opEq
    with_reducible grind only [host_function_unique]
  case label.label => exact label_children_equal children (by assumption) (by assumption) (by assumption) (by assumption)
  case frame.frame => exact frame_children_equal children (by assumption) (by assumption) (by assumption) (by assumption)
end Exec.Spec
