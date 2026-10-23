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
    (expected : List valtype) (allowed : PureHead op)
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

end Exec.Abs
