import Itasca.Runtime.SourceMachine.Core.GlobalTyping
import Itasca.Runtime.SourceMachine.Core.GlobalContents
import Itasca.Runtime.SourceMachine.Core.Simulation
import Itasca.Runtime.SourceMachine.Sim.Typing
import Itasca.Runtime.SourceMachine.Sim.Typed

namespace Itasca.Runtime.Abs.Core
open SpecExt Itasca.Runtime.Spec

/-- Resolve the owning instance's global address before reading its value. -/
def globalGet (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.GLOBALS[index]? with
  | none => .stuck
  | some address => match s.store.GLOBALS[address]? with
    | none => .stuck
    | some object => advance s {f with code := after, vals := f.vals ++ [object.VALUE]} rest

/-- Global writes retain declared mutability/type and change one payload. -/
def globalSet (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match pop f.vals, f.module.GLOBALS[index]? with
  | some (front,value), some address =>
    match s.store.GLOBALS[address]? with
    | none => .stuck
    | some object =>
      match object.TYPE with
      | .mk_globaltype none _ => .stuck
      | .mk_globaltype (some .MUT) ty =>
        if valueType value = ty then
          advance {s with store := Spec.globalWrite s.store f.toFrame index value}
            {f with code := after, vals := front} rest
        else .stuck
  | _,_ => .stuck

/-- Typed global reads are executable, preserve full source typing, and take
one generated source reduction under every active/suspended context. -/
theorem globalGet_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, globalGet ⟨s,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩
      f rest index after = .next next ∧ CoreTyped next ∧
      StepH (decode ⟨s,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code := .GLOBAL_GET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨address,object,mapped,found,continuation⟩ := global_get_frame_typed typed.contents frameTyped
  let next : AState := ⟨s,ambient,{f with code := after, vals := f.vals ++ [object.VALUE]} :: rest,[]⟩
  have fresh : ATyped next := active_frame_preservation typed.typed continuation rfl
  refine ⟨next,?_,⟨fresh,typed.contents⟩,?_⟩
  · simp only [globalGet,mapped,found,advance,next]
  · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by
      cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
    have indexWf := codeWf (.GLOBAL_GET (.mk_uN index)) (by simp)
    have bound : index < 2^32 := by
      cases indexWf with | instr_case_46 _ valid =>
      cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
    exact global_get_simulation s ambient f rest after index address object
      typed.typed.store typed.typed.ambient frameWf labelsWf valuesWf tailWf restWf
      (by simpa only [FrameHeights] using frameTyped_heights frameTyped) bound mapped found

/-- Typed writes make one source transition, preserve all store payload typing,
and leave every saved frame valid in the extended store. -/
theorem globalSet_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, globalSet ⟨s,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩
      f rest index after = .next next ∧ CoreTyped next ∧ Extend_store s next.store ∧
      StepH (decode ⟨s,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code := .GLOBAL_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,ins,outs,_,_,operation,split,operandTypes,frontWf,heights⟩ :=
    frame_typed_operands_bounds frameTyped
  cases operation
  cases operandTypes with
  | cons valueTyped tail =>
    cases tail
    rename_i value
    have decomposed : FrameTyped s
        {f with code := .GLOBAL_SET (.mk_uN index) :: after, vals := front ++ [value]} [] := by
      simpa only [split] using frameTyped
    obtain ⟨address,object,ty,mapped,found,mutable,valueOk,continuation⟩ := global_set_frame_continuation decomposed
    have extension := globalWrite_extends s f.toFrame index address object value ty
      typed.typed.store typed.contents mapped found mutable valueOk
    have contents := typed.contents.global_write typed.typed.store f.toFrame index address object value ty
      mapped found mutable valueOk
    have oldTyped := active_frame_preservation typed.typed continuation rfl
    have fresh := oldTyped.extend_same extension rfl
    let next : AState := ⟨Spec.globalWrite s f.toFrame index value,ambient,
      {f with code := after, vals := front} :: rest,[]⟩
    refine ⟨next,?_,⟨fresh,contents⟩,extension,?_⟩
    · simp only [globalSet,split,pop_append,mapped,found,mutable,value_type_of_typed valueOk,
        ite_true,advance,next]
    · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by
        cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
      have indexWf := codeWf (.GLOBAL_SET (.mk_uN index)) (by simp)
      have bound : index < 2^32 := by
        cases indexWf with | instr_case_47 _ valid =>
        cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
      have source := global_set_simulation s ambient f rest after index front value
        typed.typed.store typed.typed.ambient frameWf labelsWf frontWf (val_ok_wf valueOk)
        tailWf restWf heights bound (List.getElem?_eq_some_iff.mp mapped).1
      simpa only [split,next] using source

end Itasca.Runtime.Abs.Core
