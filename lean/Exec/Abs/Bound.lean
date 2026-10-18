import Exec.Abs.Numeric.Effect
import Exec.Abs.SliceSafety
import Exec.Abs.Measure

namespace Exec.Abs

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

theorem list_length_le_size {α : Type} [SizeOf α] (xs : List α) : xs.length ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp; omega

theorem CodeBound.measure {bound : Nat} {s : AState} (h : CodeBound bound s) :
    administrativeMeasure s ≤ bound := by
  cases hf : s.frames with
  | nil => simp [administrativeMeasure, hf]
  | cons f rest =>
    have hb := (h.frames f (by simp [hf])).1
    have hl := list_length_le_size f.code
    simp only [administrativeMeasure, hf]
    omega

/-- Every finite starting state has a finite syntactic bound. The transition
invariant below retains this same bound after recursive calls and branches. -/
theorem codeBound_initial (s : AState) : CodeBound (sizeOf s) s := by
  have hstore : sizeOf s.store < sizeOf s := by cases s; simp; omega
  have hframes : sizeOf s.frames < sizeOf s := by cases s; simp; omega
  have hfuncs : sizeOf s.store.FUNCS < sizeOf s.store := by cases s.store; simp; omega
  refine ⟨by cases s; simp; omega, ?_, ?_⟩
  · intro f hf
    have hfs := List.sizeOf_lt_of_mem hf
    have hcode : sizeOf f.code < sizeOf f := by cases f; simp; omega
    have hlabels : sizeOf f.labels < sizeOf f := by cases f; simp; omega
    refine ⟨by omega, ?_⟩
    intro label hl
    have hls := List.sizeOf_lt_of_mem hl
    have happ := list_size_append label.cont label.after
    have hlabel : sizeOf label.cont + sizeOf label.after ≤ sizeOf label := by cases label; simp; omega
    omega
  · intro fn hfn
    have hfs := List.sizeOf_lt_of_mem hfn
    cases fn with
    | MKfuncinst type module code =>
      cases code with
      | HOST host => trivial
      | FUNC index locals body =>
        change sizeOf body ≤ sizeOf s
        have hb : sizeOf body < sizeOf (funcinst.MKfuncinst type module (.FUNC index locals body)) := by simp; omega
        omega

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

theorem returnFrame_bound {bound : Nat} {s : store} {ambient : frame} {f : AFrame}
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
    (allowed : SliceInstr op)
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
  | add ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | sub ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | eqz ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | eq ty =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha, hl⟩
  | lt_u ty =>
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
  | ret => exact returnFrame_bound bounded step
  | block bt body hb =>
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
  | loop bt body hb =>
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
  | ifelse bt yes no hy hn =>
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

/-- The supported source slice is invariant along all successful steps. -/
theorem astep_bound (bound : Nat) (s next : AState) (typed : ATyped s) (slice : SliceState s) (bounded : CodeBound bound s)
    (step : astep s = .next next) : CodeBound bound next := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hslice := slice.active frame (by simp)
    have hbounded := bounded.frames frame (by simp)
    cases frame with
    | mk addr rts locals m labels code values =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, values⟩
      cases code with
      | cons op after => exact instruction_bound bound store ambient f rest op after next (hslice.1 op (by simp)) bounded step
      | nil =>
        cases labels with
        | nil => exact returnFrame_bound bounded step
        | cons label labels =>
          simp only [astep] at step
          split at step
          · apply advance_bound bounded step
            refine ⟨?_, fun l hm => hbounded.2 l (by simp [hm])⟩
            have hh := hbounded.2 label (by simp)
            have hp := list_size_append label.cont label.after
            have hpos : 1 ≤ sizeOf label.cont := by cases label.cont <;> simp <;> omega
            change sizeOf label.after ≤ bound
            omega
          · contradiction
end Exec.Abs
