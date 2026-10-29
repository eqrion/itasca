import Itasca.Runtime.SourceMachine.Sim.Compose
import Itasca.Runtime.SourceMachine.ControlSafety

namespace Itasca.Runtime.Abs.BrTable
open SpecExt Itasca.Runtime.Spec

/-- The final label is used whenever the unsigned selector is out of range. -/
def select (labels : List labelidx) (fallback : labelidx) (index : Nat) : labelidx :=
  if index < labels.length then labels[index]! else fallback

theorem select_table (labels : List labelidx) (fallback : labelidx) (index : Nat) :
    (labels ++ [fallback])[Nat.min index labels.length]? = some (select labels fallback index) := by
  by_cases bound : index < labels.length
  · simp [select,bound,Nat.min_eq_left (Nat.le_of_lt bound),List.getElem?_append,bound,getElem!_pos labels index bound]
  · simp [select,bound,Nat.min_eq_right (by omega : labels.length ≤ index),List.getElem?_append]

theorem select_size (labels : List labelidx) (fallback : labelidx) (index : Nat) :
    sizeOf (select labels fallback index) ≤ sizeOf labels + sizeOf fallback := by
  unfold select
  split
  · rename_i bound
    rw [getElem!_pos labels index bound]
    have small := List.sizeOf_lt_of_mem (List.getElem_mem bound)
    omega
  · omega

theorem select_wf {labels : List labelidx} {fallback : labelidx} (index : Nat)
    (wellFormed : wf_instr (.BR_TABLE labels fallback)) : wf_uN 32 (select labels fallback index) := by
  cases wellFormed with
  | instr_case_9 _ _ listWf fallbackWf =>
    unfold select
    split
    · rename_i bound
      rw [getElem!_pos labels index bound]
      exact listWf _ (List.getElem_mem bound)
    · exact fallbackWf

/-- BR_TABLE performs one generated source step to the selected BR. The
subsequent branch transfer reuses the ordinary BR semantics. -/
theorem simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (bits : Nat) (labels : List labelidx) (fallback : labelidx)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (hb : bits < 2 ^ integerWidth .I32) (hi : wf_instr (.BR_TABLE labels fallback)) :
    StepH (decode ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := .BR (select labels fallback bits) :: after, vals := front}::rest,[]⟩) := by
  have hbr : wf_instr (.BR (select labels fallback bits)) := .instr_case_7 _ (select_wf bits hi)
  have effect : Step_pure [admininstr_val (integerVal .I32 bits),.BR_TABLE labels fallback]
      [.BR (select labels fallback bits)] := by
    by_cases bound : bits < labels.length
    · simpa [select,bound,integerVal,admininstr_val,numtype_Inn,proj_num__0,proj_uN_0] using
        Step_pure.br_table_lt (.mk_num__0 .I32 (.mk_uN bits)) labels fallback
          (by simpa [proj_num__0,proj_uN_0] using bound) (by simp [proj_num__0])
          (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi)
          (by simpa [proj_num__0,proj_uN_0,admininstr_instr] using wf_admininstr_instr (i := .BR labels[bits]!) (by simpa only [select,if_pos bound] using hbr))
    · simpa only [select,if_neg bound,integerVal,admininstr_val,numtype_Inn] using
        Step_pure.br_table_ge (.mk_num__0 .I32 (.mk_uN bits)) labels fallback
          (by simp [proj_num__0]) (by simp [proj_num__0,proj_uN_0]; omega)
          (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi)
          (wf_admininstr_instr (i := .BR fallback) (by simpa only [select,if_neg bound] using hbr))
  simpa only [List.append_nil,List.singleton_append] using
    pure_code_simulation s ambient f rest (.BR_TABLE labels fallback)
      [.BR (select labels fallback bits)] after front [integerVal .I32 bits] [] hs ha hf hl hv hc hr heights
      (by intro v member; simp only [List.mem_singleton] at member; subst v; exact integer_val_wf .I32 bits hb)
      (forall_nil _) hi (by intro i member; simp only [List.mem_singleton] at member; subst i; exact hbr) effect

/-- Generated BR_TABLE typing makes every selectable target accept the actual
branch-value suffix, including bottom-type subtyping elimination. -/
theorem frame_preservation {s : store} {f : AFrame} {after : List instr}
    {frontValues : List val} {bits : Nat} {labels : List labelidx} {fallback : labelidx}
    (typed : FrameTyped s {f with code := .BR_TABLE labels fallback :: after, vals := frontValues ++ [integerVal .I32 bits]} []) :
    FrameTyped s {f with code := .BR (select labels fallback bits) :: after, vals := frontValues} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns code frameWf =>
    simp only [List.append_nil] at code
    obtain ⟨front,ins,outs,head,stack,tail,heights⟩ :=
      codeStack_after_bounds (value_types_concrete (frontValues ++ [integerVal .I32 bits])) code
    cases head with
    | br_table _ _ _ discarded branchTypes outputs targetBounds targetTypes defaultBound defaultTypes contextWf instructionWf =>
      have base : frontValues.map valueType = front ++ (discarded ++ branchTypes) := by
        simpa only [List.map_append,List.map_cons,List.map_nil,integerVal,valueType,
          numtype_Inn,valtype_numtype,← List.append_assoc,List.append_cancel_right_eq] using stack
      have concrete : Forall (fun ty => ty ≠ valtype.BOT) branchTypes := by
        intro ty member
        apply value_types_concrete frontValues ty
        rw [base]
        simp only [List.mem_append]
        exact Or.inr (Or.inr member)
      have selectedBound : proj_uN_0 (select labels fallback bits) < (labelContext C f.labels).LABELS.length := by
        unfold select
        split
        · rename_i bound
          rw [getElem!_pos labels bits bound]
          exact targetBounds _ (List.getElem_mem bound)
        · exact defaultBound
      have selectedTypes : proj_list_0 valtype ((labelContext C f.labels).LABELS[proj_uN_0 (select labels fallback bits)]!) = branchTypes := by
        have subtype : Resulttype_sub (.mk_list branchTypes)
            ((labelContext C f.labels).LABELS[proj_uN_0 (select labels fallback bits)]!) := by
          unfold select
          split
          · rename_i bound
            rw [getElem!_pos labels bits bound]
            exact targetTypes _ (List.getElem_mem bound)
          · exact defaultTypes
        generalize (labelContext C f.labels).LABELS[proj_uN_0 (select labels fallback bits)]! = actual at subtype ⊢
        cases actual with
        | mk_list actual => exact (concrete_result_sub_eq concrete subtype).symm
      have selectedWf : wf_instr (.BR (select labels fallback bits)) := .instr_case_7 _ (select_wf bits instructionWf)
      have head' := Instr_ok.br (labelContext C f.labels) (select labels fallback bits)
        discarded branchTypes outs selectedBound selectedTypes contextWf selectedWf
      have retained : ResultsTyped s (frontValues.map valueType) frontValues := by
        simpa using resultsTyped_take frontValues.length values
      apply FrameTyped.mk (f := {f with code := .BR (select labels fallback bits) :: after, vals := frontValues})
        C bindings localTypes locals retained returns ?_ frameWf
      simpa only [List.append_nil,base] using codeStack_prepend head' selectedWf heights tail

theorem correct (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (bits : Nat) (labels : List labelidx) (fallback : labelidx)
    (bound : bits < 2^32)
    (typed : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    ATyped ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ ∧
    NextSim ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩
      ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frameTyped : FrameTyped s {f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]} [] := by
    cases typed.frames with | cons head _ => exact head
  have restWf : Forall FrameWf rest := by
    cases typed.frames with | cons _ tail => exact framesTyped_wf tail
  obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
  have afterWf : Forall wf_instr after := fun i member => codeWf i (List.mem_cons_of_mem _ member)
  have opWf := codeWf (.BR_TABLE labels fallback) (List.mem_cons_self ..)
  have frontWf : Forall wf_val front := fun v member => valuesWf v (List.mem_append_left _ member)
  have heights : ∀ label ∈ f.labels, label.height ≤ front.length := by
    obtain ⟨C,first,operands,ins,outs,bindings,locals,head,split,operandTypes,firstWf,bounds⟩ := frame_typed_operands_bounds (f := {f with vals := front ++ [integerVal .I32 bits]}) frameTyped
    cases head with
    | br_table =>
      have sizes := congrArg List.length split
      have operandSizes := operandTypes.length_eq
      simp only [List.length_append,List.length_singleton] at sizes operandSizes
      intro label member
      have small := bounds label member
      omega
  exact ⟨active_frame_preservation typed (frame_preservation frameTyped) rfl,
    NextSim.single (simulation s ambient f rest after front bits labels fallback typed.store typed.ambient
      frameWf labelsWf frontWf afterWf restWf heights bound opWf)⟩

theorem operands {s : store} {f : AFrame} {after : List instr}
    {labels : List labelidx} {fallback : labelidx}
    (typed : FrameTyped s {f with code := .BR_TABLE labels fallback :: after} []) :
    ∃ front bits, f.vals = front ++ [integerVal .I32 bits] ∧ bits < 2^32 := by
  obtain ⟨C,first,operands,ins,outs,bindings,locals,head,split,operandTypes⟩ := frame_typed_operands typed
  cases head with
  | br_table =>
    obtain ⟨discarded,remaining,rfl,_,remainingTyped⟩ := resultsTyped_split operandTypes
    obtain ⟨arguments,selector,rfl,_,selectorTyped⟩ := resultsTyped_split remainingTyped
    cases selectorTyped with
    | cons value empty =>
      cases empty
      obtain ⟨bits,rfl,bound⟩ := integer_val_inv (ty := .I32) value
      refine ⟨first ++ discarded ++ arguments,bits,?_,bound⟩
      simpa only [List.append_assoc] using split

end Itasca.Runtime.Abs.BrTable
