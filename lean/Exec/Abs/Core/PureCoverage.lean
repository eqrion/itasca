import Exec.Abs.Core.Step
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety

namespace Exec.Abs

theorem core_replace_frame {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} (h : CoreState ⟨s, ambient, f :: rest, []⟩)
    (hf : FrameCore f') : CoreState ⟨s, ambient, f' :: rest, []⟩ := by
  refine ⟨?_, h.functions⟩
  intro frame hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact hf
  · exact h.active frame (by simp [hm])

theorem advance_core {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} {next : AState} (h : CoreState ⟨s, ambient, f :: rest, []⟩)
    (step : advance ⟨s, ambient, f :: rest, []⟩ f' rest = .next next)
    (hf : FrameCore f') : CoreState next := by
  simp only [advance, AResult.next.injEq] at step
  rw [← step]
  exact core_replace_frame h hf

theorem returnFrame_core {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {next : AState} (h : CoreState ⟨s, ambient, f :: rest, []⟩)
    (step : returnFrame ⟨s, ambient, f :: rest, []⟩ f rest = .next next) : CoreState next := by
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

theorem branch_core {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {depth : Nat} {next : AState} (h : CoreState ⟨s, ambient, f :: rest, []⟩)
    (step : branch ⟨s, ambient, f :: rest, []⟩ f rest depth = .next next) : CoreState next := by
  simp only [branch] at step
  split at step
  · contradiction
  · rename_i target lookup
    split at step
    · apply advance_core h step
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
theorem call_core {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {index : Nat} {after : List instr} {next : AState}
    (h : CoreState ⟨s, ambient, f :: rest, []⟩) (ha : Forall CoreInstr after)
    (step : call ⟨s, ambient, f :: rest, []⟩ f rest index after = .next next) : CoreState next := by
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
              simp only [call,resolve,lookup,ht,hc] at step
              repeat' first | split at step | contradiction
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
theorem instruction_core (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (allowed : SliceInstr op)
    (slice : CoreState ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) :
    CoreState next := by
  have hf := slice.active { f with code := op :: after } (by simp)
  have ha : Forall CoreInstr after := fun i hm => hf.1 i (by simp [hm])
  have hl := hf.2
  cases allowed with
  | numeric descriptor =>
    obtain ⟨values, rfl⟩ := Numeric.astep_effect ⟨s, ambient, [], []⟩ f rest after descriptor next step
    exact advance_core slice rfl ⟨ha, hl⟩
  | nop => exact advance_core slice step ⟨ha, hl⟩
  | unreachable => simp [astep] at step
  | const ty value =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | drop =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | add ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | sub ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | eqz ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | eq ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | lt_u ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | local_get index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | local_set index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | local_tee index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_core slice step ⟨ha, hl⟩
  | br index => cases index with | mk_uN i => exact branch_core slice step
  | call index => cases index with | mk_uN i => exact call_core slice ha step
  | ret => exact returnFrame_core slice step
  | block bt body hb =>
    have hb : Forall CoreInstr body := fun i member => .slice (hb i member)
    simp only [astep, enterLabel, Bool.false_eq_true, ite_false] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_core slice step
      refine ⟨hb, ?_⟩
      intro label hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨by simp [Forall], ha⟩
      · exact hl label hm
  | loop bt body hb =>
    have hb : Forall CoreInstr body := fun i member => .slice (hb i member)
    simp only [astep, enterLabel, ite_true] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_core slice step
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
    have hy : Forall CoreInstr yes := fun i member => .slice (hy i member)
    have hn : Forall CoreInstr no := fun i member => .slice (hn i member)
    simp only [astep] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_core slice step
      refine ⟨?_, hl⟩
      intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · apply CoreInstr.block
        first | assumption | split <;> assumption
      · exact ha i hi
  | br_if index =>
    cases index with
    | mk_uN i =>
      simp only [astep] at step
      repeat' first | split at step | contradiction
      all_goals
        apply advance_core slice step
        first
        | exact ⟨ha, hl⟩
        | refine ⟨?_, hl⟩
          intro op hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact .slice (.br _)
          · exact ha op hm


end Exec.Abs
