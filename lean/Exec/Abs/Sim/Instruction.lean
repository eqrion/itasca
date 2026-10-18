import Exec.Abs.Numeric.TransitionSimulation
import Exec.Abs.Sim.Structured

namespace Exec.Abs
open SpecExt Exec.Spec

/-- Every successful instruction in the checked integer slice has a counted
source simulation; only moving a constant is an administrative stutter. -/
theorem instruction_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (slice : SliceInstr op)
    (typed : ATyped ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ next := by
  have hf : FrameTyped s { f with code := op :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact framesTyped_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frameTyped_wf hf
  have hafter : Forall wf_instr after := fun i hm => hc i (by simp [hm])
  have hi : wf_instr op := hc op (by simp)
  have hheights := frameTyped_heights hf
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
  | add ty => exact typed_binop_simulation s ambient f rest after ty .ADD (Or.inl rfl) next typed step
  | sub ty => exact typed_binop_simulation s ambient f rest after ty .SUB (Or.inr rfl) next typed step
  | eqz ty => exact typed_eqz_simulation s ambient f rest after ty next typed step
  | eq ty => exact typed_relop_simulation s ambient f rest after ty .EQ (Or.inl rfl) next typed step
  | lt_u ty => exact typed_relop_simulation s ambient f rest after ty (.LT .U) (Or.inr rfl) next typed step
  | block bt body _ => exact typed_block_simulation s ambient f rest after bt body next typed step
  | loop bt body _ => exact typed_loop_simulation s ambient f rest after bt body next typed step
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
  | ifelse bt yes no _ _ =>
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop
    obtain ⟨args, conditions, rfl, hargs, hcond⟩ := resultsTyped_split hoperands
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
        typed.store typed.ambient hw hl (forall_append hfirst (resultsTyped_wf hargs)) hafter hr
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
      obtain ⟨args, conditions, rfl, hargs, hcond⟩ := resultsTyped_split hoperands
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
          typed.store typed.ambient hw hl (forall_append hfirst (resultsTyped_wf hargs)) hafter hr
          (by intro label hm; have hh := heights label hm; simp only [List.length_append]; omega) hb hi32
        simpa only [← hvals] using result

end Exec.Abs
