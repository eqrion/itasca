import Exec.Abs.Core.Typing
import Exec.Abs.Preservation
import Exec.Abs.Sim.Typed

namespace Exec.Abs.Core
open SpecExt Exec.Spec

def select (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match pop f.vals with
  | some (remaining,condition) => match integer .I32 condition, pop remaining with
    | some bits, some (remaining,right) => match pop remaining with
      | some (front,left) =>
        if valueType left = valueType right then
          advance s {f with code := after, vals := front ++ [if bits = 0 then right else left]} rest
        else .stuck
      | none => .stuck
    | _,_ => .stuck
  | none => .stuck

theorem select_frame_preservation {s : store} {f : AFrame} {after : List instr}
    {front : List val} {left right : val} {bits : Nat}
    (typed : FrameTyped s {f with code := .SELECT none :: after, vals := front ++ [left,right,integerVal .I32 bits]} []) :
    FrameTyped s {f with code := after, vals := front ++ [if bits = 0 then right else left]} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,operation,stack,continuation⟩ :=
      codeStack_after (value_types_concrete (front ++ [left,right,integerVal .I32 bits])) hc
    cases operation with
    | select_impl _ ty type numeric vector sub allowed contextWf instructionWf =>
      simp only [List.map_append,List.map_cons,List.map_nil] at stack
      have length : (front.map valueType).length = base.length := by
        have lengths := congrArg List.length stack
        simp only [List.length_append,List.length_cons,List.length_nil] at lengths
        omega
      obtain ⟨baseEq,types⟩ := List.append_inj stack length
      simp only [List.cons.injEq] at types
      have leftType : valueType left = ty := types.1
      have rightType : valueType right = ty := types.2.1
      have selectedTyped : Val_ok s (if bits = 0 then right else left) ty := by
        split
        · simpa only [rightType] using resultsTyped_self_mem (value := right) values (by simp)
        · simpa only [leftType] using resultsTyped_self_mem (value := left) values (by simp)
      have selectedType := value_type_of_typed selectedTyped
      have prefixTyped : ResultsTyped s (front.map valueType) front := by
        simpa using resultsTyped_take front.length values
      apply FrameTyped.mk (f := {f with code := after, vals := front ++ [if bits = 0 then right else left]}) C
        bindings localTypes locals ?_ returns ?_ hw
      · simpa only [ResultsTyped,List.map_append,List.map_cons,List.map_nil,selectedType] using
          List.rel_append prefixTyped (List.Forall₂.cons selectedTyped List.Forall₂.nil)
      · simpa only [List.map_append,List.map_cons,List.map_nil,List.append_nil,selectedType,baseEq] using continuation

theorem select_simulation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (left right : val) (bits : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (leftWf : wf_val left) (rightWf : wf_val right) (bitsBound : bits < 2^32) :
    StepH (decode ⟨s,ambient,
      {f with code := .SELECT none :: after, vals := front ++ [left,right,integerVal .I32 bits]} :: rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := after, vals := front ++ [if bits = 0 then right else left]} :: rest,[]⟩) := by
  have conditionWf := integer_val_wf .I32 bits bitsBound
  have selectWf : wf_instr (.SELECT none) := .instr_case_3 _
  apply pure_stack_simulation s ambient f rest (.SELECT none) after front
    [left,right,integerVal .I32 bits] [if bits = 0 then right else left]
    hs ha hf hl hv hc hr heights
  · simpa [Forall] using And.intro leftWf (And.intro rightWf conditionWf)
  · by_cases zero : bits = 0 <;> simp [zero,Forall,leftWf,rightWf]
  · exact selectWf
  · by_cases zero : bits = 0
    · simpa [vals,integerVal,admininstr_val,admininstr_instr,numtype_Inn,zero] using
        Step_pure.select_false left right (.mk_num__0 .I32 (.mk_uN bits)) none
          (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0]) leftWf rightWf
          (.admininstr_case_13 _ _ (integer_num_wf .I32 bits bitsBound)) (wf_admininstr_instr selectWf)
    · simpa [vals,integerVal,admininstr_val,admininstr_instr,numtype_Inn,zero] using
        Step_pure.select_true left right (.mk_num__0 .I32 (.mk_uN bits)) none
          (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0]) leftWf rightWf
          (.admininstr_case_13 _ _ (integer_num_wf .I32 bits bitsBound)) (wf_admininstr_instr selectWf)

/-- The generated select rule supplies two equally typed alternatives and an
i32 condition, so the executable branch is total on every typed frame. -/
theorem select_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .SELECT none :: after} :: rest,[]⟩) :
    ∃ next, select ⟨s,ambient,{f with code := .SELECT none :: after} :: rest,[]⟩
      f rest after = .next next ∧ CoreTyped next ∧
      StepH (decode ⟨s,ambient,{f with code := .SELECT none :: after} :: rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code := .SELECT none :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,ins,outs,_,_,operation,split,operandTypes,frontWf,heights⟩ :=
    frame_typed_operands_bounds frameTyped
  cases operation
  cases operandTypes with
  | cons leftTyped tail =>
    cases tail with
    | cons rightTyped tail =>
      cases tail with
      | cons conditionTyped tail =>
        cases tail
        rename_i left right condition
        obtain ⟨bits,rfl,bitsBound⟩ := integer_val_inv (ty := .I32) conditionTyped
        have matching : valueType left = valueType right :=
          (value_type_of_typed leftTyped).trans (value_type_of_typed rightTyped).symm
        have continuation := select_frame_preservation (bits := bits) (by simpa only [split] using frameTyped)
        have fresh := active_frame_preservation typed.typed continuation rfl
        let next : AState := ⟨s,ambient,
          {f with code := after, vals := front ++ [if bits = 0 then right else left]} :: rest,[]⟩
        refine ⟨next,?_,⟨fresh,typed.contents⟩,?_⟩
        · have shape : f.vals = ((front ++ [left]) ++ [right]) ++ [integerVal .I32 bits] := by
            simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
          have decoded : integer .I32 (integerVal .I32 bits) = some bits := by
            simpa only [numtype_Inn] using integer_accepts .I32 bits bitsBound
          simp only [select,shape,pop_append,decoded,matching,
            ite_true,advance,next]
        · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by
            cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
          have source := select_simulation s ambient f rest after front left right bits
            typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
            (val_ok_wf leftTyped) (val_ok_wf rightTyped) bitsBound
          simpa only [split,next] using source

end Exec.Abs.Core
