import Exec.Spec.Choices.RedexDecomposition
import Exec.Spec.Choices.ContextSyntax
namespace Exec.Spec
open SpecExt

theorem CoreChoiceStep.nonactive_in_context {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {state : _root_.state} {body : List admininstr} {events : List HostEvent} {after : config}
    (source : CoreChoiceStep choices occurrence ⟨state,body⟩ events after)
    (front : List val) (tail : List admininstr)
    (nonactive : activeTrap (vals front++(body++tail))=false) : activeTrap body=false := by
  have suffix := stepH_activeTrap_suffix (source.toChoiceStep.erases admissible) tail
  dsimp only [trapCode] at suffix
  rw [activeTrap_vals,suffix] at nonactive
  exact nonactive

theorem core_context_unique {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {state : _root_.state} {front otherFront : List val}
    {body otherBody tail otherTail : List admininstr} {events otherEvents : List HostEvent} {after otherAfter : config}
    (first : CoreChoiceStep choices occurrence ⟨state,body⟩ events after)
    (second : CoreChoiceStep choices occurrence ⟨state,otherBody⟩ otherEvents otherAfter)
    (nonactive : activeTrap (vals front++(body++tail))=false)
    (same : vals front++(body++tail)=vals otherFront++(otherBody++otherTail)) :
    front=otherFront ∧ body=otherBody ∧ tail=otherTail := by
  have firstActive := first.nonactive_in_context admissible front tail nonactive
  have otherActive : activeTrap (vals otherFront++(otherBody++otherTail))=false := by rw [← same]; exact nonactive
  have secondActive := second.nonactive_in_context admissible otherFront otherTail otherActive
  obtain ⟨args,operation,shape,nonvalue,arity⟩ := first.input_shape firstActive
  obtain ⟨otherArgs,otherOperation,otherShape,otherNonvalue,otherArity⟩ := second.input_shape secondActive
  rw [shape,otherShape] at same
  obtain ⟨frontEq,argsEq,opEq,tailEq⟩ := operand_context_unique state nonvalue otherNonvalue arity otherArity same
  refine ⟨frontEq,?_,tailEq⟩
  rw [shape,otherShape,argsEq,opEq]

theorem sizeOf_instruction_context (front : List val) (body tail : List admininstr) :
    sizeOf body≤sizeOf (vals front++(body++tail)) := by
  have first := sizeOf_admin_append (vals front) (body++tail)
  have second := sizeOf_admin_append body tail
  have frontPositive := sizeOf_admin_positive (vals front)
  have tailPositive := sizeOf_admin_positive tail
  omega

theorem ContextualCore.view {choices : SourceChoices} {occurrence : Nat} {before after : config}
    {events : List HostEvent} (source : ContextualCore choices occurrence before events after) :
    ∃ z z' front body result tail,
      before=⟨z,vals front++(body++tail)⟩ ∧ after=⟨z',vals front++(result++tail)⟩ ∧
      CoreChoiceStep choices occurrence ⟨z,body⟩ events ⟨z',result⟩ := by
  cases source
  exact ⟨_,_,_,_,_,_,rfl,rfl,by assumption⟩
end Exec.Spec
