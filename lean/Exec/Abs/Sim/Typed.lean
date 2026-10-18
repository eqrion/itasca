import Exec.Abs.StepSafety
import Exec.Abs.Sim.Call
import Exec.Abs.Sim.Trap
import Exec.Abs.Sim.Local

namespace Exec.Abs
open SpecExt Exec.Spec

/-- A successful abstract step either performs positive source work or is an
exact decoding stutter that strictly decreases the administrative potential. -/
def NextSim (s next : AState) : Prop :=
  (decode s = decode next ∧ administrativeMeasure next < administrativeMeasure s) ∨
  ∃ n, 0 < n ∧ StepsHN n (decode s) [] (decode next)

theorem NextSim.single {s next : AState} (h : StepH (decode s) [] (decode next)) : NextSim s next :=
  Or.inr ⟨1, by omega, by simpa only [List.nil_append] using StepsHN.cons h (StepsHN.refl (stepH_wf h).2)⟩

theorem NextSim.counted {s next : AState} {n : Nat}
    (h : StepsHN n (decode s) [] (decode next)) (hn : 0 < n) : NextSim s next :=
  Or.inr ⟨n, hn, h⟩

/-- Operand inversion also proves that no consumed value belongs to a saved
outer label prefix. -/
theorem frame_typed_operands_bounds {s : store} {f : AFrame} {op : instr} {code : List instr}
    (h : FrameTyped s { f with code := op :: code } []) :
    ∃ C first operands ins outs,
      ModuleBindings s f.module C ∧ C.LOCALS = f.locals.map valueType ∧
      Instr_ok (labelContext C f.labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      f.vals = first ++ operands ∧ ResultsTyped s ins operands ∧
      Forall wf_val first ∧ (∀ label ∈ f.labels, label.height ≤ first.length) := by
  cases h with
  | mk C bindings locals hlocals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, heq, heights⟩ := codeStack_head_bounds (value_types_concrete f.vals) hc
    have values' : ResultsTyped s (front ++ ins) f.vals := by rw [← heq]; exact values
    obtain ⟨first, operands, hsplit, hfirst, hoperands⟩ := resultsTyped_split values'
    refine ⟨C, first, operands, ins, outs, bindings, locals, hop, hsplit, hoperands,
      resultsTyped_wf hfirst, ?_⟩
    intro label hm
    rw [resultsTyped_length hfirst]
    exact heights label hm

theorem typed_binop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (ty : Inn) (op : binop_Inn)
    (allowed : op = .ADD ∨ op = .SUB) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: after } :: rest, []⟩ next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    have hafter : Forall wf_instr after := fun i hm => hc i (by simp [hm])
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop
    cases hoperands with
    | cons hlv hrv =>
      cases hrv with
      | cons hrv hend =>
        cases hend
        obtain ⟨a, rfl, ha⟩ := integer_val_inv hlv
        obtain ⟨b, rfl, hb⟩ := integer_val_inv hrv
        have hfa := integer_accepts ty a ha
        have hfb := integer_accepts ty b hb
        have hwidth : (if numtype_Inn ty = numtype.I32 then 32 else 64) = integerWidth ty := by cases ty <;> rfl
        have hpop : pop f.vals = some (first ++ [integerVal ty a], integerVal ty b) := by
          rw [hsplit, show first ++ [integerVal ty a, integerVal ty b] = (first ++ [integerVal ty a]) ++ [integerVal ty b] by simp]
          exact pop_append _ _
        rcases allowed with rfl | rfl
        · have result := integer_add_simulation s ambient f rest after first ty a b ha hb
            typed.store typed.ambient hw hl hfirst hafter (framesTyped_wf hr) heights
          simp only [astep, hpop, pop_append, hfa, hfb, hwidth, if_pos rfl, ite_true, integerBinary, advance, AResult.next.injEq] at step
          rw [← step]
          apply NextSim.single
          simpa only [← hsplit] using result
        · have result := integer_sub_simulation s ambient f rest after first ty a b ha hb
            typed.store typed.ambient hw hl hfirst hafter (framesTyped_wf hr) heights
          simp only [astep, hpop, pop_append, hfa, hfb, hwidth, if_pos rfl, ite_true, integerBinary, advance, AResult.next.injEq] at step
          rw [← step]
          apply NextSim.single
          simpa only [← hsplit] using result

theorem typed_eqz_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (ty : Inn) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after } :: rest, []⟩ next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop
    cases hoperands with
    | cons hv hend =>
      cases hend
      obtain ⟨bits, rfl, hb⟩ := integer_val_inv hv
      have hi := integer_accepts ty bits hb
      have result := integer_eqz_simulation s ambient f rest after first ty bits hb
        typed.store typed.ambient hw hl hfirst (fun i hm => hc i (by simp [hm])) (framesTyped_wf hr) heights
      have hnext : next = ⟨s, ambient, { f with code := after, vals := first ++ [integerVal .I32 (if bits = 0 then 1 else 0)] } :: rest, []⟩ := by
        simpa [astep, hsplit, pop_append, hi, advance] using step.symm
      rw [hnext]
      apply NextSim.single
      simpa only [← hsplit] using result

theorem typed_relop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (ty : Inn) (op : relop_Inn)
    (allowed : op = .EQ ∨ op = .LT .U) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: after } :: rest, []⟩ next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop
    cases hoperands with
    | cons hlv hrv =>
      cases hrv with
      | cons hrv hend =>
        cases hend
        obtain ⟨a, rfl, ha⟩ := integer_val_inv hlv
        obtain ⟨b, rfl, hb⟩ := integer_val_inv hrv
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
          apply NextSim.single
          have result := integer_relop_simulation s ambient f rest after first ty .EQ a b _ ha hb hb'
            (integer_eq_relation ty a b) typed.store typed.ambient hw hl hfirst
            (fun i hm => hc i (by simp [hm])) (framesTyped_wf hr) heights
          simpa only [← hsplit] using result
        · have hnext : next = ⟨s, ambient, { f with code := after, vals := first ++ [integerVal .I32 (if a < b then 1 else 0)] } :: rest, []⟩ := by
            simpa [astep, hpop, pop_append, hfa, hfb, advance] using step.symm
          rw [hnext]
          have hb' : (if a < b then 1 else 0) < 2 ^ integerWidth .I32 := by split <;> decide
          apply NextSim.single
          have result := integer_relop_simulation s ambient f rest after first ty (.LT .U) a b _ ha hb hb'
            (integer_ltu_relation ty a b) typed.store typed.ambient hw hl hfirst
            (fun i hm => hc i (by simp [hm])) (framesTyped_wf hr) heights
          simpa only [← hsplit] using result

end Exec.Abs
