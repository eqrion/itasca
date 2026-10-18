import Exec.Abs.Numeric.TransitionSafety
import Exec.Abs.CallSafety

namespace Exec.Abs
open SpecExt Exec.Spec

/-- The checked binary typing rule supplies two concrete integer operands. -/
theorem binop_operands {s : store} {f : AFrame} {after : List instr} {ty : Inn} {op : binop_Inn}
    (h : FrameTyped s { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: after } []) :
    ∃ first a b, f.vals = first ++ [integerVal ty a, integerVal ty b] ∧
      a < 2 ^ integerWidth ty ∧ b < 2 ^ integerWidth ty := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop
  cases hoperands with
  | cons hl hr =>
    cases hr with
    | cons hr hend =>
      cases hend
      obtain ⟨a, rfl, ha⟩ := integer_val_inv hl
      obtain ⟨b, rfl, hb⟩ := integer_val_inv hr
      exact ⟨first, a, b, hsplit, ha, hb⟩

theorem binop_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (ty : Inn) (op : binop_Inn) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: after } :: rest, []⟩ = .next next) :
    ATyped next := by
  exact Numeric.astep_preservation s ambient f rest after (.binary ty op) next typed step

theorem eqz_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (ty : Inn) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after } :: rest, []⟩ = .next next) :
    ATyped next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands hf
    cases hop
    cases hoperands with
    | cons hv hend =>
      cases hend
      obtain ⟨bits, rfl, hb⟩ := integer_val_inv hv
      have hi := integer_accepts ty bits hb
      have hnext : next = ⟨s, ambient, { f with code := after, vals := first ++ [integerVal .I32 (if bits = 0 then 1 else 0)] } :: rest, []⟩ := by
        simpa [astep, hsplit, pop_append, hi, advance] using step.symm
      rw [hnext]
      have hb' : (if bits = 0 then 1 else 0) < 2 ^ integerWidth .I32 := by split <;> decide
      apply active_frame_preservation typed (integer_testop_frame_preservation (ty := ty) (op := .EQZ) (bits := bits) typed.store hb' ?_) rfl
      simpa only [hsplit] using hf

theorem relop_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (ty : Inn) (op : relop_Inn)
    (allowed : op = .EQ ∨ op = .LT .U) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: after } :: rest, []⟩ = .next next) :
    ATyped next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands hf
    cases hop
    cases hoperands with
    | cons hl hr =>
      cases hr with
      | cons hr hend =>
        cases hend
        obtain ⟨a, rfl, ha⟩ := integer_val_inv hl
        obtain ⟨b, rfl, hb⟩ := integer_val_inv hr
        have hfa := integer_accepts ty a ha
        have hfb := integer_accepts ty b hb
        have hpop : pop f.vals = some (first ++ [integerVal ty a], integerVal ty b) := by
          rw [hsplit, show first ++ [integerVal ty a, integerVal ty b] = (first ++ [integerVal ty a]) ++ [integerVal ty b] by simp]
          exact pop_append _ _
        rcases allowed with rfl | rfl
        · have hnext : next = ⟨s, ambient, { f with code := after, vals := first ++ [integerVal .I32 (if a = b then 1 else 0)] } :: rest, []⟩ := by
            simpa [astep, hpop, pop_append, hfa, hfb, advance] using step.symm
          rw [hnext]
          have hb' : (if a = b then 1 else 0) < 2 ^ integerWidth .I32 := by split <;> decide
          apply active_frame_preservation typed (integer_relop_frame_preservation (ty := ty) (op := .EQ) (a := a) (b := b) typed.store hb' ?_) rfl
          simpa only [hsplit] using hf
        · have hnext : next = ⟨s, ambient, { f with code := after, vals := first ++ [integerVal .I32 (if a < b then 1 else 0)] } :: rest, []⟩ := by
            simpa [astep, hpop, pop_append, hfa, hfb, advance] using step.symm
          rw [hnext]
          have hb' : (if a < b then 1 else 0) < 2 ^ integerWidth .I32 := by split <;> decide
          apply active_frame_preservation typed (integer_relop_frame_preservation (ty := ty) (op := .LT .U) (a := a) (b := b) typed.store hb' ?_) rfl
          simpa only [hsplit] using hf

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
    (slice : SliceInstr op)
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
  | add ty => exact binop_preservation s ambient f rest after ty .ADD next typed step
  | sub ty => exact binop_preservation s ambient f rest after ty .SUB next typed step
  | eqz ty => exact eqz_preservation s ambient f rest after ty next typed step
  | eq ty => exact relop_preservation s ambient f rest after ty .EQ (Or.inl rfl) next typed step
  | lt_u ty => exact relop_preservation s ambient f rest after ty (.LT .U) (Or.inr rfl) next typed step
  | block bt body _ => exact block_preservation s ambient f rest after bt body next typed step
  | loop bt body _ => exact loop_preservation s ambient f rest after bt body next typed step
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
  | ifelse bt yes no _ _ =>
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

/-- One step of the initial integer machine preserves its source typing
invariant, including nested labels, calls, and returns. -/
theorem astep_preservation (s next : AState) (typed : ATyped s) (slice : SliceState s)
    (step : astep s = .next next) : ATyped next := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hf : FrameTyped store frame [] := by
      cases typed.frames with | cons h _ => exact h
    have hslice := (slice.active frame (by simp)).1
    cases frame with
    | mk addr rts locals m labels code values =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, values⟩
      cases code with
      | cons op after =>
        exact instruction_preservation store ambient f rest op after next (hslice op (by simp)) typed step
      | nil =>
        cases labels with
        | nil =>
          have hv := frame_end_typed (f := f) hf
          change ResultsTyped store rts values at hv
          have hlen := resultsTyped_length hv
          have hv' : ResultsTyped store rts (values.drop (values.length - rts.length)) := by
            simpa only [hlen, Nat.sub_self, List.drop_zero] using hv
          exact returnFrame_preservation typed hv' step
        | cons label labels =>
          simp only [astep] at step
          split at step
          · simp only [advance, AResult.next.injEq] at step
            rw [← step]
            exact active_frame_preservation typed (label_exit_frame_preservation (f := f) hf) rfl
          · contradiction

end Exec.Abs
