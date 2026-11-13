import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Measure

/-!
Sections, each formerly its own module: StepSafety, Bound.
-/

/-! ## StepSafety -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem return_frame_preservation {s : store} {ambient : frame} {f : AFrame}
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
  | ret => exact return_frame_preservation typed (return_suffix_typed hf) step
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
    obtain ⟨args, conditions, rfl, _, hcond⟩ := results_typed_split hoperands
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
      obtain ⟨args, conditions, rfl, _, hcond⟩ := results_typed_split hoperands
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

end Itasca.Runtime.SourceMachine

end

/-! ## Bound -/

section

/-!
Source-code bounds for frames, continuations and machine states. Execution and resource arguments retain these bounds through control and store transitions.
-/

namespace Itasca.Runtime.SourceMachine

/-- Code sizes include nested bodies. Saved branch continuations are bounded
as the exact sequence resumed by a branch. Values, locals, and call depth do
not enter this invariant and cannot increase its fixed bound. -/
def FrameCodeBound (bound : Nat) (f : AFrame) : Prop :=
  sizeOf f.code ≤ bound ∧ ∀ label ∈ f.labels, sizeOf (label.cont ++ label.after) ≤ bound

structure CodeBound (bound : Nat) (s : AState) : Prop where
  positive : 1 ≤ bound
  frames : Forall (FrameCodeBound bound) s.frames
  functions : ∀ fn ∈ s.store.FUNCS, match fn.CODE with
    | .HOST _ => True
    | .FUNC _ _ body => sizeOf body ≤ bound

theorem list_size_append {α : Type} [SizeOf α] (xs ys : List α) :
    sizeOf (xs ++ ys) + 1 = sizeOf xs + sizeOf ys := by
  induction xs with
  | nil => simp; omega
  | cons x xs ih => simp_all; omega

theorem bound_replace_frame {bound : Nat} {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} (h : CodeBound bound ⟨s, ambient, f :: rest, []⟩)
    (hf : FrameCodeBound bound f') : CodeBound bound ⟨s, ambient, f' :: rest, []⟩ := by
  refine ⟨h.positive, ?_, h.functions⟩
  intro frame hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact hf
  · exact h.frames frame (by simp [hm])

theorem advance_bound {bound : Nat} {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} {next : AState} (h : CodeBound bound ⟨s, ambient, f :: rest, []⟩)
    (step : advance ⟨s, ambient, f :: rest, []⟩ f' rest = .next next)
    (hf : FrameCodeBound bound f') : CodeBound bound next := by
  simp only [advance, AResult.next.injEq] at step
  rw [← step]
  exact bound_replace_frame h hf

theorem return_frame_bound {bound : Nat} {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {next : AState} (h : CodeBound bound ⟨s, ambient, f :: rest, []⟩)
    (step : returnFrame ⟨s, ambient, f :: rest, []⟩ f rest = .next next) : CodeBound bound next := by
  simp only [returnFrame] at step
  split at step
  · cases rest with
    | nil =>
      simp only [AResult.next.injEq] at step
      rw [← step]
      exact ⟨h.positive, by simp [Forall], h.functions⟩
    | cons caller callers =>
      simp only [advance, AResult.next.injEq] at step
      rw [← step]
      refine ⟨h.positive, ?_, h.functions⟩
      intro frame hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact h.frames caller (by simp)
      · exact h.frames frame (by simp [hm])
  · contradiction

theorem branch_bound {bound : Nat} {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {depth : Nat} {next : AState} (h : CodeBound bound ⟨s, ambient, f :: rest, []⟩)
    (step : branch ⟨s, ambient, f :: rest, []⟩ f rest depth = .next next) : CodeBound bound next := by
  simp only [branch] at step
  split at step
  · contradiction
  · rename_i target lookup
    split at step
    · apply advance_bound h step
      have ht := (h.frames f (by simp)).2 target (List.mem_of_getElem? lookup)
      refine ⟨ht, ?_⟩
      intro label hm
      exact (h.frames f (by simp)).2 label (List.mem_of_mem_drop hm)
    · contradiction

/-- Code-bearing store entries are unchanged by the integer slice; a defined
call selects a body already covered by the store's slice invariant. -/
theorem call_bound {bound : Nat} {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {index : Nat} {after : List instr} {next : AState}
    (h : CodeBound bound ⟨s, ambient, f :: rest, []⟩) (ha : sizeOf after ≤ bound)
    (step : call ⟨s, ambient, f :: rest, []⟩ f rest index after = .next next) : CodeBound bound next := by
  cases resolve : f.module.FUNCS[index]? with
  | none => simp [call, resolve] at step
  | some address =>
    cases lookup : s.FUNCS[address]? with
    | none => simp [call, resolve, lookup] at step
    | some fn =>
      have hfn := h.functions fn (List.mem_of_getElem? lookup)
      cases ht : fn.TYPE with
      | mk_functype params results =>
        cases params with
        | mk_list params =>
          cases results with
          | mk_list results =>
            cases hc : fn.CODE with
            | HOST host =>
              simp only [call, resolve, lookup, ht, hc] at step
              repeat' first | split at step | contradiction
            | FUNC fi locals body =>
              simp only [hc] at hfn
              simp only [call, resolve, lookup, ht, hc] at step
              repeat' first | split at step | contradiction
              simp only [AResult.next.injEq] at step
              rw [← step]
              refine ⟨h.positive, ?_, h.functions⟩
              intro frame hm
              simp only [List.mem_cons] at hm
              rcases hm with rfl | rfl | hm
              · exact ⟨hfn, by simpa [Forall] using h.positive⟩
              · exact ⟨ha, (h.frames f (by simp)).2⟩
              · exact h.frames frame (by simp [hm])

/-- The source instruction families are closed under each successful abstract
transition, including code introduced by structured control. -/
theorem instruction_bound (bound : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (allowed : PureHead op)
    (bounded : CodeBound bound ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) :
    CodeBound bound next := by
  have hf := bounded.frames { f with code := op :: after } (by simp)
  have ha : sizeOf after ≤ bound := by have hh := hf.1; simp at hh; omega
  have hl := hf.2
  cases allowed with
  | numeric descriptor =>
    obtain ⟨values, rfl⟩ := Numeric.astep_effect ⟨s, ambient, [], []⟩ f rest after descriptor next step
    exact advance_bound bounded rfl ⟨ha, hl⟩
  | nop => exact advance_bound bounded step ⟨ha, hl⟩
  | unreachable => simp [astep] at step
  | const ty value =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | drop =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | local_get index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | local_set index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | local_tee index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | br index => cases index with | mk_uN i => exact branch_bound bounded step
  | call index => cases index with | mk_uN i => exact call_bound bounded ha step
  | ret => exact return_frame_bound bounded step
  | block bt body =>
    simp only [astep, enterLabel, Bool.false_eq_true, ite_false] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_bound bounded step
      refine ⟨by have hh := hf.1; simp at hh ⊢; omega, ?_⟩
      intro label hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ha
      · exact hl label hm
  | loop bt body =>
    simp only [astep, enterLabel, ite_true] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_bound bounded step
      refine ⟨by have hh := hf.1; simp at hh ⊢; omega, ?_⟩
      intro label hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · simpa using hf.1
      · exact hl label hm
  | ifelse bt yes no =>
    simp only [astep] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_bound bounded step
      refine ⟨?_, hl⟩
      have hh := hf.1
      simp at hh ⊢
      omega
  | br_if index =>
    cases index with
    | mk_uN i =>
      simp only [astep] at step
      repeat' first | split at step | contradiction
      all_goals
        apply advance_bound bounded step
        refine ⟨?_, hl⟩
        have hh := hf.1
        simp at hh ⊢
        omega

end Itasca.Runtime.SourceMachine

end
