import Exec.Abs.Numeric.TransitionSafety
import Exec.Abs.CallSafety

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem returnFrame_preservation {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {next : AState}
    (typed : ATyped ⟨s, ambient, f :: rest, []⟩)
    (values : ResultsTyped s f.resultTypes (f.vals.drop (f.vals.length - f.arity)))
    (step : returnFrame ⟨s, ambient, f :: rest, []⟩ f rest = .next next) : ATyped next := by
  have hp := return_values_preservation typed values
  unfold returnFrame at step
  split at step
  · cases rest with
    | nil =>
      simp only [AResult.next.injEq] at step
      exact step ▸ hp
    | cons caller callers =>
      simp only [advance, AResult.next.injEq] at step
      exact step ▸ hp
  · contradiction

/-- Preservation for every supported instruction, using generated typing
inversion to recover operands and continuation types. -/
theorem instruction_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (slice : PureHead op)
    (typed : ATyped ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) : ATyped next := by
  have hf : FrameTyped s { f with code := op :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  cases slice with
  | numeric descriptor => exact Numeric.astep_preservation s ambient f rest after descriptor next typed step
  | nop =>
    simp only [astep, advance, AResult.next.injEq] at step
    exact step ▸ nop_preservation s ambient f rest after [] typed
  | unreachable => simp [astep] at step
  | const ty value =>
    simp only [astep] at step
    split at step
    · simp only [advance, AResult.next.injEq] at step
      exact step ▸ const_preservation s ambient f rest after _ _ [] typed
    · contradiction
  | block bt body => exact block_preservation s ambient f rest after bt body next typed step
  | loop bt body => exact loop_preservation s ambient f rest after bt body next typed step
  | br index => cases index with | mk_uN i => exact br_preservation s ambient f rest after i next typed step
  | call index => cases index with | mk_uN i => exact call_preservation s ambient f rest after i next typed step
  | ret => exact returnFrame_preservation typed (return_suffix_typed hf) step
  | drop =>
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands hf
    cases hop
    cases hoperands with
    | cons hv hend =>
      cases hend
      rename_i value
      simp only [astep, hsplit, pop_append, advance, AResult.next.injEq] at step
      rw [← step]
      apply active_frame_preservation typed (drop_frame_preservation (f := f) (code := after) (baseValues := first) (value := value) ?_) rfl
      simpa only [hsplit] using hf
  | local_get index =>
    cases index with
    | mk_uN i =>
      simp only [astep] at step
      split at step
      · contradiction
      · rename_i value lookup
        have hi : i < f.locals.length := List.getElem?_eq_some_iff.mp lookup |>.1
        have heq : value = f.locals[i]! := by
          simpa only [List.getElem?_eq_getElem hi, Option.some.injEq, getElem!_pos f.locals i hi] using lookup.symm
        subst value
        simp only [advance, AResult.next.injEq] at step
        exact step ▸ active_frame_preservation typed (local_get_frame_preservation hf) rfl
  | local_set index =>
    cases index with
    | mk_uN i =>
      obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands hf
      cases hop
      cases hoperands with
      | cons hv hend =>
        cases hend
        simp only [astep, hsplit, pop_append] at step
        split at step
        · rename_i popped operand old hpop hlookup
          simp only [Option.some.injEq, Prod.mk.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          split at step
          · simp only [ite_true, advance, AResult.next.injEq] at step
            rw [← step]
            apply active_frame_preservation typed (local_set_frame_preservation (f := f) (code := after) (index := i) ?_) rfl
            simpa only [hsplit] using hf
          · contradiction
        · contradiction
  | local_tee index =>
    cases index with
    | mk_uN i =>
      obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands hf
      cases hop
      cases hoperands with
      | cons hv hend =>
        cases hend
        simp only [astep, hsplit, pop_append] at step
        split at step
        · rename_i popped operand old hpop hlookup
          simp only [Option.some.injEq, Prod.mk.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          split at step
          · simp only [reduceCtorEq, ite_false, advance, AResult.next.injEq] at step
            rw [← step]
            apply active_frame_preservation typed (local_tee_frame_preservation (f := f) (code := after) (index := i) ?_) rfl
            simpa only [hsplit] using hf
          · contradiction
        · contradiction
  | ifelse bt yes no =>
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands hf
    cases hop
    obtain ⟨args, conditions, rfl, _, hcond⟩ := resultsTyped_split hoperands
    cases hcond with
    | cons hv hend =>
      cases hend
      obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hv
      have hi : integer .I32 (integerVal .I32 bits) = some bits := integer_accepts .I32 bits hb
      have hvals : f.vals = (first ++ args) ++ [integerVal .I32 bits] := by simpa only [List.append_assoc] using hsplit
      simp only [astep, hvals, pop_append, hi, advance, AResult.next.injEq] at step
      rw [← step]
      apply active_frame_preservation typed (if_frame_preservation (f := f) ?_) rfl
      simpa only [hvals] using hf
  | br_if index =>
    cases index with
    | mk_uN i =>
      obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands hf
      cases hop
      obtain ⟨args, conditions, rfl, _, hcond⟩ := resultsTyped_split hoperands
      cases hcond with
      | cons hv hend =>
        cases hend
        obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hv
        have hi : integer .I32 (integerVal .I32 bits) = some bits := integer_accepts .I32 bits hb
        have hvals : f.vals = (first ++ args) ++ [integerVal .I32 bits] := by simpa only [List.append_assoc] using hsplit
        simp only [astep, hvals, pop_append, hi, advance, AResult.next.injEq] at step
        rw [← step]
        apply active_frame_preservation typed (br_if_frame_preservation (f := f) ?_) rfl
        simpa only [hvals] using hf

end Itasca.Runtime.Abs
