import Exec.Abs.Numeric.Effect
import Exec.Abs.Invoke

namespace Exec.Abs
open SpecExt Exec.Spec

/-- The outermost active function retains the invocation's declared results;
inner callees may have independent signatures. -/
inductive FramesReturn (expected : List valtype) : List AFrame → Prop where
  | last {f : AFrame} : f.resultTypes = expected → FramesReturn expected [f]
  | under {f : AFrame} {rest : List AFrame} : FramesReturn expected rest → FramesReturn expected (f :: rest)

/-- Attach an invocation signature until all frames finish, then require its
actual returned values to have that exact signature. -/
def InvocationResult (expected : List valtype) (s : AState) : Prop :=
  match s.frames with
  | [] => ResultsTyped s.store expected s.results
  | frames => FramesReturn expected frames

theorem FramesReturn.replace {expected : List valtype} {f f' : AFrame} {rest : List AFrame}
    (h : FramesReturn expected (f :: rest)) (same : f'.resultTypes = f.resultTypes) :
    FramesReturn expected (f' :: rest) := by
  cases h with
  | last result => exact .last (same.trans result)
  | under rest => exact .under rest

theorem entry_result (s : store) (ambient : frame) (address : funcaddr)
    (moduleInst : moduleinst) (results : List valtype) (body : List instr)
    (args defaults : List val) :
    InvocationResult results (entryState s ambient address moduleInst results body args defaults) :=
  .last rfl

theorem advance_result {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} {next : AState} {expected : List valtype}
    (h : InvocationResult expected ⟨s, ambient, f :: rest, []⟩)
    (step : advance ⟨s, ambient, f :: rest, []⟩ f' rest = .next next)
    (same : f'.resultTypes = f.resultTypes) : InvocationResult expected next := by
  simp only [advance, AResult.next.injEq] at step
  rw [← step]
  exact FramesReturn.replace h same

theorem returnFrame_result {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {next : AState} {expected : List valtype}
    (typed : ATyped ⟨s, ambient, f :: rest, []⟩)
    (h : InvocationResult expected ⟨s, ambient, f :: rest, []⟩)
    (step : returnFrame ⟨s, ambient, f :: rest, []⟩ f rest = .next next) : InvocationResult expected next := by
  have values : ResultsTyped s (f.vals.map valueType) f.vals := by
    cases typed.frames with
    | cons hf _ => cases hf; assumption
  have suffix : ResultsTyped s ((f.vals.drop (f.vals.length - f.arity)).map valueType)
      (f.vals.drop (f.vals.length - f.arity)) := by
    simpa only [ResultsTyped, List.map_drop] using List.forall₂_drop (f.vals.length - f.arity) values
  simp only [returnFrame] at step
  split at step
  · rename_i valid
    rw [valid.2] at suffix
    cases rest with
    | nil =>
      simp only [AResult.next.injEq] at step
      rw [← step]
      change FramesReturn expected [f] at h
      cases h with
      | last result => simpa only [InvocationResult, result] using suffix
      | under rest => cases rest
    | cons caller callers =>
      simp only [advance, AResult.next.injEq] at step
      rw [← step]
      change FramesReturn expected (f :: caller :: callers) at h
      cases h with
      | under rest => exact FramesReturn.replace rest rfl
  · contradiction

theorem call_result {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {index : Nat} {after : List instr} {next : AState} {expected : List valtype}
    (h : InvocationResult expected ⟨s, ambient, f :: rest, []⟩)
    (step : call ⟨s, ambient, f :: rest, []⟩ f rest index after = .next next) : InvocationResult expected next := by
  simp only [call] at step
  repeat' first | split at step | contradiction
  all_goals
    simp only [AResult.next.injEq] at step
    rw [← step]
    exact FramesReturn.under (FramesReturn.replace h rfl)

/-- Signature preservation depends on the source type invariant only when the
last frame returns actual values; other steps preserve the outermost frame. -/
theorem instruction_result (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (expected : List valtype) (allowed : SliceInstr op)
    (typed : ATyped ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (h : InvocationResult expected ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) :
    InvocationResult expected next := by
  cases allowed with
  | numeric descriptor =>
    obtain ⟨values, rfl⟩ := Numeric.astep_effect ⟨s, ambient, [], []⟩ f rest after descriptor next step
    exact advance_result h rfl rfl
  | call index => cases index with | mk_uN i => exact call_result h step
  | ret => exact returnFrame_result typed h step
  | _ =>
    simp only [astep, integerBinary, branch, enterLabel] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_result h step rfl

theorem astep_result (s next : AState) (expected : List valtype)
    (typed : ATyped s) (slice : SliceState s) (result : InvocationResult expected s)
    (step : astep s = .next next) : InvocationResult expected next := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hslice := (slice.active frame (by simp)).1
    cases frame with
    | mk addr rts locals m labels code values =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, values⟩
      cases code with
      | cons op after => exact instruction_result store ambient f rest op after next expected (hslice op (by simp)) typed result step
      | nil =>
        cases labels with
        | nil => exact returnFrame_result typed result step
        | cons label labels =>
          simp only [astep] at step
          split at step
          · exact advance_result result step rfl
          · contradiction

/-- The expected result types follow through every actual successful step. -/
theorem run_result {n : Nat} {s next : AState} {events : List HostEvent}
    (run : Iterations SuccessfulStep n s events next) (expected : List valtype)
    (typed : ATyped s) (slice : SliceState s) (result : InvocationResult expected s) :
    InvocationResult expected next := by
  induction run with
  | refl _ => exact result
  | cons step _ ih =>
    obtain ⟨_, step⟩ := step
    exact ih (astep_preservation _ _ typed slice step) (astep_slice _ _ typed slice step)
      (astep_result _ _ expected typed slice result step)

theorem run_invariants {n : Nat} {s next : AState} {events : List HostEvent}
    (run : Iterations SuccessfulStep n s events next) (typed : ATyped s) (slice : SliceState s) :
    ATyped next ∧ SliceState next := by
  induction run with
  | refl _ => exact ⟨typed, slice⟩
  | cons step _ ih =>
    obtain ⟨_, step⟩ := step
    exact ih (astep_preservation _ _ typed slice step) (astep_slice _ _ typed slice step)

theorem done_frames_empty (s : AState) (typed : ATyped s) (slice : SliceState s)
    (values : List val) (step : astep s = .done values) : s.frames = [] := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => rfl
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hslice := (slice.active frame (by simp)).1
    cases frame with
    | mk addr rts locals m labels code operands =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, operands⟩
      cases code with
      | nil =>
        simp only [astep, returnFrame, advance] at step
        repeat' first | contradiction | split at step
      | cons op after => exact False.elim (instruction_not_done store ambient f rest op after (hslice op (by simp)) values step)

/-- Normal return produces values of the external invocation's declared type. -/
theorem done_results_typed (s : AState) (expected : List valtype) (values : List val)
    (typed : ATyped s) (slice : SliceState s) (result : InvocationResult expected s)
    (step : astep s = .done values) : ResultsTyped s.store expected values := by
  have empty := done_frames_empty s typed slice values step
  simp only [InvocationResult, empty] at result
  have same : s.results = values := by simpa only [astep, empty, AResult.done.injEq] using step
  simpa only [same] using result

/-- A finite successful invocation run followed by normal return has the
expected results and a quantitative specification execution to those values. -/
theorem run_done {n : Nat} {s next : AState} {events : List HostEvent}
    (run : Iterations SuccessfulStep n s events next) (expected : List valtype) (values : List val)
    (typed : ATyped s) (slice : SliceState s) (result : InvocationResult expected s)
    (done : astep next = .done values) :
    ResultsTyped next.store expected values ∧
      ∃ count, StepsHN count (decode s) events ⟨⟨next.store, next.ambient⟩, vals values⟩ ∧
        n / (sizeOf s + 1) ≤ count := by
  obtain ⟨typed', slice'⟩ := run_invariants run typed slice
  have result' := run_result run expected typed slice result
  refine ⟨done_results_typed next expected values typed' slice' result' done, ?_⟩
  obtain ⟨count, reduction, bound⟩ := run_progress run typed slice
  rw [done_simulation next typed' slice' values done] at reduction
  exact ⟨count, reduction, bound⟩

end Exec.Abs
