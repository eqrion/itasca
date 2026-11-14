import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.Sim.Control

/-!
Sections, each formerly its own module: Instruction, Step, Terminal, Compose, Host.
-/

/-! ## Instruction -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Every successful instruction in the checked integer slice has a counted
source simulation; only moving a constant is an administrative stutter. -/
theorem instruction_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (slice : PureHead op)
    (typed : ATyped ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ next := by
  have hf : FrameTyped s { f with code := op :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact frames_typed_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frame_typed_wf hf
  have hafter : Forall wf_instr after := fun i hm => hc i (by simp [hm])
  have hi : wf_instr op := hc op (by simp)
  have hheights := frame_typed_heights hf
  cases slice with
  | numeric descriptor => exact Numeric.astep_simulation s ambient f rest after descriptor next typed step
  | nop =>
    simp only [astep, advance, AResult.next.injEq] at step
    rw [← step]
    exact .single (nop_simulation s ambient f rest after typed.store typed.ambient hw hl hv hafter hr)
  | unreachable => simp [astep] at step
  | const ty value =>
    simp only [astep] at step
    split at step
    · simp only [advance, AResult.next.injEq] at step
      rw [← step]
      exact Or.inl ⟨decode_const s ambient f rest _ _ after hheights,
        const_measure_decreases s ambient f rest _ _ after⟩
    · contradiction
  | block bt body => exact typed_block_simulation s ambient f rest after bt body next typed step
  | loop bt body => exact typed_loop_simulation s ambient f rest after bt body next typed step
  | br index =>
    cases index with
    | mk_uN i => exact .counted (typed_branch_simulation s ambient f rest after i next typed step) (by omega)
  | call index =>
    cases index with
    | mk_uN i => exact .counted (typed_call_simulation s ambient f rest after i next typed step) (by omega)
  | ret => exact .counted (typed_return_simulation s ambient f rest after next typed step) (by omega)
  | drop =>
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop
    cases hoperands with
    | cons hvalue hend =>
      cases hend
      rename_i value
      simp only [astep, hsplit, pop_append, advance, AResult.next.injEq] at step
      rw [← step]
      apply NextSim.single
      have result := drop_simulation s ambient f rest after first value typed.store typed.ambient hw hl hfirst
        (val_ok_wf hvalue) hafter hr heights
      simpa only [← hsplit] using result
  | local_get index =>
    cases index with
    | mk_uN i =>
      have hi32 : i < 2 ^ 32 := by
        cases hi with
        | instr_case_43 _ hu => cases hu with
          | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
      simp only [astep] at step
      split at step
      · contradiction
      · rename_i value lookup
        have hb : i < f.locals.length := List.getElem?_eq_some_iff.mp lookup |>.1
        have heq : value = f.locals[i]! := by
          simpa only [List.getElem?_eq_getElem hb, Option.some.injEq, getElem!_pos f.locals i hb] using lookup.symm
        subst value
        simp only [advance, AResult.next.injEq] at step
        rw [← step]
        exact .single (local_get_simulation s ambient f rest after i typed.store typed.ambient hw hl hv hafter hr
          hheights hb hi32)
  | local_set index =>
    cases index with
    | mk_uN i =>
      have hi32 : i < 2 ^ 32 := by
        cases hi with
        | instr_case_44 _ hu => cases hu with
          | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
      obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
      cases hop
      cases hoperands with
      | cons hvalue hend =>
        cases hend
        simp only [astep, hsplit, pop_append] at step
        split at step
        · rename_i popped operand old hpop hlookup
          simp only [Option.some.injEq, Prod.mk.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          split at step
          · simp only [ite_true, advance, AResult.next.injEq] at step
            rw [← step]
            apply NextSim.single
            have result := local_set_simulation s ambient f rest after first _ i typed.store typed.ambient
              hw hl hfirst (val_ok_wf hvalue) hafter hr heights hi32
            simpa only [← hsplit] using result
          · contradiction
        · contradiction
  | local_tee index =>
    cases index with
    | mk_uN i =>
      have hi32 : i < 2 ^ 32 := by
        cases hi with
        | instr_case_45 _ hu => cases hu with
          | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
      obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
      cases hop
      cases hoperands with
      | cons hvalue hend =>
        cases hend
        simp only [astep, hsplit, pop_append] at step
        split at step
        · rename_i popped operand old hpop hlookup
          simp only [Option.some.injEq, Prod.mk.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          split at step
          · simp only [reduceCtorEq, ite_false, advance, AResult.next.injEq] at step
            rw [← step]
            have result := local_tee_simulation s ambient f rest after first _ i typed.store typed.ambient
              hw hl hfirst (val_ok_wf hvalue) hafter hr heights hi32
            apply NextSim.counted (n := 2) ?_ (by omega)
            simpa only [← hsplit] using result
          · contradiction
        · contradiction
  | ifelse bt yes no =>
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop
    obtain ⟨args, conditions, rfl, hargs, hcond⟩ := results_typed_split hoperands
    cases hcond with
    | cons hvalue hend =>
      cases hend
      obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hvalue
      have hbits : integer .I32 (integerVal .I32 bits) = some bits := integer_accepts .I32 bits hb
      have hvals : f.vals = (first ++ args) ++ [integerVal .I32 bits] := by simpa only [List.append_assoc] using hsplit
      simp only [astep, hvals, pop_append, hbits, advance, AResult.next.injEq] at step
      rw [← step]
      apply NextSim.single
      have result := if_simulation s ambient f rest after (first ++ args) bits bt yes no
        typed.store typed.ambient hw hl (forall_append hfirst (results_typed_wf hargs)) hafter hr
        (by intro label hm; have hh := heights label hm; simp only [List.length_append]; omega) hb hi
      simpa only [← hvals] using result
  | br_if index =>
    cases index with
    | mk_uN i =>
      have hi32 : i < 2 ^ 32 := by
        cases hi with
        | instr_case_8 _ hu => cases hu with
          | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
      obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
      cases hop
      obtain ⟨args, conditions, rfl, hargs, hcond⟩ := results_typed_split hoperands
      cases hcond with
      | cons hvalue hend =>
        cases hend
        obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hvalue
        have hbits : integer .I32 (integerVal .I32 bits) = some bits := integer_accepts .I32 bits hb
        have hvals : f.vals = (first ++ args) ++ [integerVal .I32 bits] := by simpa only [List.append_assoc] using hsplit
        simp only [astep, hvals, pop_append, hbits, advance, AResult.next.injEq] at step
        rw [← step]
        apply NextSim.single
        have result := br_if_simulation s ambient f rest after (first ++ args) bits i
          typed.store typed.ambient hw hl (forall_append hfirst (results_typed_wf hargs)) hafter hr
          (by intro label hm; have hh := heights label hm; simp only [List.length_append]; omega) hb hi32
        simpa only [← hvals] using result

end Itasca.Runtime.SourceMachine

end

/-! ## Step -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem typed_label_end_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (label : Label) (labels : List Label) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩ next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, hv, _⟩ := frame_typed_wf hf
    have nested : ∀ outer ∈ labels, outer.height ≤ label.height := by
      cases hf with
      | mk C _ _ _ _ _ code _ => exact (code_stack_labels_nested code).1
    have heights := frame_typed_heights hf
    have result := label_exit_simulation s ambient f rest label labels typed.store typed.ambient hw hl hv
      (frames_typed_wf hr) (heights label (by simp)) nested
    simp only [astep] at step
    split at step
    · simp only [advance, AResult.next.injEq] at step
      rw [← step]
      exact .single result
    · contradiction

end Itasca.Runtime.SourceMachine

end

/-! ## Terminal -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Scalar integer traps arise from an explicit unreachable instruction or a numeric operation. -/
theorem instruction_trap_eq (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (allowed : PureHead op)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .trap) :
    op = .UNREACHABLE ∨ ∃ descriptor : Numeric.Instruction, op = descriptor.source := by
  cases allowed
  case numeric descriptor => exact .inr ⟨descriptor, rfl⟩
  case unreachable => exact .inl rfl
  all_goals
    simp only [astep, advance, integerBinary, branch, enterLabel, call, returnFrame] at step
    repeat' first | contradiction | split at step

end Itasca.Runtime.SourceMachine

end

/-! ## Compose -/

section

namespace Itasca.Runtime.SourceMachine
open Itasca.Runtime.Spec

/-- Fusing source administrative instructions preserves counted simulation.
Positive reductions compose; a decoding stutter contributes no source steps. -/
theorem NextSim.trans {first middle last : AState}
    (left : NextSim first middle) (right : NextSim middle last) : NextSim first last := by
  rcases left with ⟨same, decrease⟩ | ⟨n, positive, steps⟩
  · rcases right with ⟨same', decrease'⟩ | ⟨n, positive, steps⟩
    · exact Or.inl ⟨same.trans same', Nat.lt_trans decrease' decrease⟩
    · exact Or.inr ⟨n, positive, by simpa only [same] using steps⟩
  · rcases right with ⟨same', _⟩ | ⟨m, positive', steps'⟩
    · exact Or.inr ⟨n, positive, by simpa only [same'] using steps⟩
    · exact Or.inr ⟨n + m, by omega, by simpa only [List.nil_append] using steps.trans steps'⟩

end Itasca.Runtime.SourceMachine

end

/-! ## Host -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- A direct host call resolves its module index and then returns atomically.
The host event and changed store survive all labels and suspended callers. -/
theorem host_return_simulation (s s' : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (baseValues args results : List val) (events : List HostEvent)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : f.module.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32)
    (hargs : Forall wf_val args)
    (host : StepH ⟨⟨s,f.toFrame⟩,vals args ++ [.CALL_ADDR address]⟩ events
      ⟨⟨s',f.toFrame⟩,vals results⟩) :
    StepsHN 2
      (decode ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after,vals := baseValues ++ args} :: rest,[]⟩)
      events
      (decode ⟨s',ambient,{f with code := after,vals := baseValues ++ results} :: rest,[]⟩) := by
  have first := step_h_active ambient rest f.arity
    (step_h_decode_labels
      (step_h_instrs (call_resolve s f.toFrame index address hs hf resolve hi32)
        args (after.map admininstr_instr) hargs (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have second := step_h_active ambient rest f.arity
    (step_h_decode_labels (step_h_instrs host [] (after.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  simp only [vals,List.map_nil,List.nil_append,List.append_assoc] at first second
  have both := StepsHN.cons first (StepsHN.cons second (StepsHN.refl (step_h_wf second).2))
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights,decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame,admininstr_instr] using both

/-- Host traps retain callback store effects while the source semantics unwinds
all remaining labels and callers. Unwinding emits no additional host events. -/
theorem host_trap_simulation (s s' : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (baseValues args : List val) (events : List HostEvent)
    (hs : wf_store s) (hs' : wf_store s') (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : f.module.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32)
    (hargs : Forall wf_val args)
    (host : StepH ⟨⟨s,f.toFrame⟩,vals args ++ [.CALL_ADDR address]⟩ events
      ⟨⟨s',f.toFrame⟩,[.TRAP]⟩) :
    ∃ n, 2 ≤ n ∧ StepsHN n
      (decode ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after,vals := baseValues ++ args} :: rest,[]⟩)
      events ⟨⟨s',ambient⟩,[.TRAP]⟩ := by
  have first := step_h_active ambient rest f.arity
    (step_h_decode_labels
      (step_h_instrs (call_resolve s f.toFrame index address hs hf resolve hi32)
        args (after.map admininstr_instr) hargs (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have second := step_h_active ambient rest f.arity
    (step_h_decode_labels (step_h_instrs host [] (after.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have frames : Forall FrameWf ({f with vals := baseValues,code := after} :: rest) := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨hf,hl,hv,hc⟩
    · exact hr frame member
  obtain ⟨n,tail⟩ := trap_frames s' ambient ({f with vals := baseValues,code := after} :: rest) hs' ha frames
  have tail' : StepsHN n _ [] ⟨⟨s',ambient⟩,[.TRAP]⟩ := tail
  simp only [vals,List.map_nil,List.nil_append,List.append_assoc] at first second
  have both := StepsHN.cons first (StepsHN.cons second tail')
  refine ⟨n+2,by omega,?_⟩
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeFrames,instrContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame,admininstr_instr,Nat.add_assoc] using both
end Itasca.Runtime.SourceMachine

end
