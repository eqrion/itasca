import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety

namespace Exec.Abs

abbrev FrameSlice (f : AFrame) : Prop :=
  Forall SliceInstr f.code ∧ Forall (fun label =>
    Forall SliceInstr label.cont ∧ Forall SliceInstr label.after) f.labels

theorem slice_replace_frame {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} (h : SliceState ⟨s, ambient, f :: rest, []⟩)
    (hf : FrameSlice f') : SliceState ⟨s, ambient, f' :: rest, []⟩ := by
  refine ⟨?_, h.functions⟩
  intro frame hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact hf
  · exact h.active frame (by simp [hm])

theorem advance_slice {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} {next : AState} (h : SliceState ⟨s, ambient, f :: rest, []⟩)
    (step : advance ⟨s, ambient, f :: rest, []⟩ f' rest = .next next)
    (hf : FrameSlice f') : SliceState next := by
  simp only [advance, AResult.next.injEq] at step
  rw [← step]
  exact slice_replace_frame h hf

theorem returnFrame_slice {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {next : AState} (h : SliceState ⟨s, ambient, f :: rest, []⟩)
    (step : returnFrame ⟨s, ambient, f :: rest, []⟩ f rest = .next next) : SliceState next := by
  simp only [returnFrame] at step
  split at step
  · cases rest with
    | nil =>
      simp only [AResult.next.injEq] at step
      rw [← step]
      exact ⟨by simp [Forall], h.functions⟩
    | cons caller callers =>
      simp only [advance, AResult.next.injEq] at step
      rw [← step]
      refine ⟨?_, h.functions⟩
      intro frame hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact h.active caller (by simp)
      · exact h.active frame (by simp [hm])
  · contradiction

theorem branch_slice {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {depth : Nat} {next : AState} (h : SliceState ⟨s, ambient, f :: rest, []⟩)
    (step : branch ⟨s, ambient, f :: rest, []⟩ f rest depth = .next next) : SliceState next := by
  simp only [branch] at step
  split at step
  · contradiction
  · rename_i target lookup
    split at step
    · apply advance_slice h step
      have ht := (h.active f (by simp)).2 target (List.mem_of_getElem? lookup)
      refine ⟨?_, ?_⟩
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact ht.1 i hi
        · exact ht.2 i hi
      · intro label hm
        exact (h.active f (by simp)).2 label (List.mem_of_mem_drop hm)
    · contradiction

/-- Code-bearing store entries are unchanged by the integer slice; a defined
call selects a body already covered by the store's slice invariant. -/
theorem call_slice {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {index : Nat} {after : List instr} {next : AState}
    (h : SliceState ⟨s, ambient, f :: rest, []⟩) (ha : Forall SliceInstr after)
    (step : call ⟨s, ambient, f :: rest, []⟩ f rest index after = .next next) : SliceState next := by
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
            | HOST host => simp [hc] at hfn
            | FUNC fi locals body =>
              simp only [hc] at hfn
              simp only [call, resolve, lookup, ht, hc] at step
              repeat' first | split at step | contradiction
              simp only [AResult.next.injEq] at step
              rw [← step]
              refine ⟨?_, h.functions⟩
              intro frame hm
              simp only [List.mem_cons] at hm
              rcases hm with rfl | rfl | hm
              · exact ⟨hfn, by simp [Forall]⟩
              · exact ⟨ha, (h.active f (by simp)).2⟩
              · exact h.active frame (by simp [hm])


/-- The source instruction families are closed under each successful abstract
transition, including code introduced by structured control. -/
theorem instruction_slice (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (allowed : SliceInstr op)
    (slice : SliceState ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) :
    SliceState next := by
  have hf := slice.active { f with code := op :: after } (by simp)
  have ha : Forall SliceInstr after := fun i hm => hf.1 i (by simp [hm])
  have hl := hf.2
  cases allowed with
  | numeric descriptor =>
    obtain ⟨values, rfl⟩ := Numeric.astep_effect ⟨s, ambient, [], []⟩ f rest after descriptor next step
    exact advance_slice slice rfl ⟨ha, hl⟩
  | nop => exact advance_slice slice step ⟨ha, hl⟩
  | unreachable => simp [astep] at step
  | const ty value =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | drop =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | add ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | sub ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | eqz ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | eq ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | lt_u ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | local_get index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | local_set index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | local_tee index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_slice slice step ⟨ha, hl⟩
  | br index => cases index with | mk_uN i => exact branch_slice slice step
  | call index => cases index with | mk_uN i => exact call_slice slice ha step
  | ret => exact returnFrame_slice slice step
  | block bt body hb =>
    simp only [astep, enterLabel, Bool.false_eq_true, ite_false] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_slice slice step
      refine ⟨hb, ?_⟩
      intro label hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨by simp [Forall], ha⟩
      · exact hl label hm
  | loop bt body hb =>
    simp only [astep, enterLabel, ite_true] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_slice slice step
      refine ⟨hb, ?_⟩
      intro label hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · refine ⟨?_, ha⟩
        intro i hi
        simp only [List.mem_singleton] at hi
        subst i
        exact .loop bt body hb
      · exact hl label hm
  | ifelse bt yes no hy hn =>
    simp only [astep] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_slice slice step
      refine ⟨?_, hl⟩
      intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · apply SliceInstr.block
        first | assumption | split <;> assumption
      · exact ha i hi
  | br_if index =>
    cases index with
    | mk_uN i =>
      simp only [astep] at step
      repeat' first | split at step | contradiction
      all_goals
        apply advance_slice slice step
        first
        | exact ⟨ha, hl⟩
        | refine ⟨?_, hl⟩
          intro op hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact .br _
          · exact ha op hm

/-- The supported source slice is invariant along all successful steps. -/
theorem astep_slice (s next : AState) (typed : ATyped s) (slice : SliceState s)
    (step : astep s = .next next) : SliceState next := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hslice := slice.active frame (by simp)
    cases frame with
    | mk addr rts locals m labels code values =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, values⟩
      cases code with
      | cons op after => exact instruction_slice store ambient f rest op after next (hslice.1 op (by simp)) slice step
      | nil =>
        cases labels with
        | nil => exact returnFrame_slice slice step
        | cons label labels =>
          simp only [astep] at step
          split at step
          · apply advance_slice slice step
            exact ⟨(hslice.2 label (by simp)).2, fun l hm => hslice.2 l (by simp [hm])⟩
          · contradiction

end Exec.Abs
