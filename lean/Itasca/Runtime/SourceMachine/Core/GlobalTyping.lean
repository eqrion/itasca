import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.SourceMachine.Preservation

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- The canonical global typing rule and actual module binding identify a
concrete, correctly typed global value and its continuation. -/
theorem global_get_frame_typed {s : store} {f : AFrame} {code : List instr}
    {index : Nat} (contents : StoreContentsTyped s)
    (h : FrameTyped s { f with code := .GLOBAL_GET (.mk_uN index) :: code } []) :
    ∃ address object, f.module.GLOBALS[index]? = some address ∧
      s.GLOBALS[address]? = some object ∧
      FrameTyped s {f with code := code, vals := f.vals ++ [object.VALUE]} [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front,ins,outs,hop,hstack,hafter⟩ := code_stack_after (value_types_concrete f.vals) hc
    cases hop with
    | global_get _ _ ty mutable hi ht _ _ =>
      have bound : index < C.GLOBALS.length := by simpa [labelContext,proj_uN_0] using hi
      have sourceType : C.GLOBALS[index]? = some (.mk_globaltype mutable ty) := by
        simp only [labelContext,proj_uN_0] at ht
        simpa [getElem!_pos, bound] using congrArg some ht
      obtain ⟨address,object,mapped,found,typed⟩ := bindings.global_lookup sourceType
      have value := contents.global_value found typed
      have actualType := value_type_of_typed value
      refine ⟨address,object,mapped,found,?_⟩
      apply FrameTyped.mk (f := {f with code := code, vals := f.vals ++ [object.VALUE]}) C
        bindings localTypes locals ?_ returns ?_ hw
      · simpa only [ResultsTyped,List.map_append,List.map_cons,List.map_nil,actualType] using
          List.rel_append values (List.Forall₂.cons value List.Forall₂.nil)
      · simp only [List.append_nil] at hstack
        simpa only [List.map_append,List.map_cons,List.map_nil,List.append_nil,hstack,actualType] using hafter

/-- Popping a typed global.set operand preserves the code continuation in the
old store. The separate typed content update then transports this frame. -/
theorem global_set_frame_continuation {s : store} {f : AFrame} {code : List instr}
    {index : Nat} {front : List val} {value : val}
    (h : FrameTyped s {f with code := .GLOBAL_SET (.mk_uN index) :: code, vals := front ++ [value]} []) :
    ∃ address object ty, f.module.GLOBALS[index]? = some address ∧
      s.GLOBALS[address]? = some object ∧ object.TYPE = .mk_globaltype (some .MUT) ty ∧
      Val_ok s value ty ∧ FrameTyped s {f with code := code, vals := front} [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,hop,hstack,hafter⟩ :=
      code_stack_after (value_types_concrete (front ++ [value])) hc
    cases hop with
    | global_set _ _ ty hi ht _ _ =>
      have bound : index < C.GLOBALS.length := by simpa [labelContext,proj_uN_0] using hi
      have sourceType : C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) := by
        simp only [labelContext,proj_uN_0] at ht
        simpa [getElem!_pos, bound] using congrArg some ht
      obtain ⟨address,object,mapped,found,typed⟩ := bindings.global_lookup sourceType
      simp only [List.map_append,List.map_cons,List.map_nil] at hstack
      have sameLength : (front.map valueType).length = base.length := by
        have lengths := congrArg List.length hstack
        simp only [List.length_append,List.length_cons,List.length_nil] at lengths
        omega
      obtain ⟨baseEq,lastEq⟩ := List.append_inj hstack sameLength
      have valueTypeEq : valueType value = ty := by simpa using lastEq
      have valueTyped : Val_ok s value ty := by
        have self := results_typed_self_mem (value := value) values (by simp)
        simpa only [valueTypeEq] using self
      refine ⟨address,object,ty,mapped,found,typed,valueTyped,?_⟩
      have prefixTyped : ResultsTyped s (front.map valueType) front := by
        simpa using results_typed_take front.length values
      apply FrameTyped.mk (f := {f with code := code, vals := front}) C
        bindings localTypes locals prefixTyped returns ?_ hw
      simpa only [List.append_nil,baseEq] using hafter

end Itasca.Runtime.SourceMachine
