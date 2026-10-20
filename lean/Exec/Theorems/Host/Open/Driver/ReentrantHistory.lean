import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Itasca.Support.Result
import Exec.Interp.Control.LoopOpenDivergence
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

def Outcome.history {M : Type} : Outcome M → List Observation
  | .host _ history | .invocation _ history => history

def outputHistory {M : Type} : ControlFlow (State M) (Outcome M) → List Observation
  | .cont state => state.history
  | .done outcome => outcome.history

theorem acceptCall_history {M : Type} (select : Selector) (state : State M)
    (phase : Interp.OpenCall.CallPhase M Unit) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) :
    ∃events,(acceptCall select state phase root results).history=state.history++events := by
  cases phase with
  | done answer => exact ⟨[],(List.append_nil _).symm⟩
  | pending exec store token address base identity args defaults => exact ⟨_,rfl⟩

/-- Every actual completed tick preserves the full expanded observation
prefix. This property needs neither termination nor a machine certificate. -/
theorem tick_history {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) (state : State M) (out : ControlFlow (State M) (Outcome M))
    (actual : tick memory floats allocator select state=.ok out) :
    ∃events,outputHistory out=state.history++events := by
  unfold tick at actual
  repeat' first
    | (simp only [Std.bind_assoc,bind_ok] at actual)
    | (split at actual)
    | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
       cases value
       try simp only [Std.uncurry] at actual)
    | (simp only [Result.ok.injEq] at actual
       cases actual
       simp only [outputHistory,Outcome.history,List.append_assoc]
       first | exact acceptCall_history _ _ _ _ _ | exact ⟨[],(List.append_nil _).symm⟩ | exact ⟨_,rfl⟩)

/-- Every finite actual continuing prefix retains all earlier observations. -/
theorem continuing_history {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) {count : Nat} {first last : State M}
    (trace : Interp.ContinuingTrace (tick memory floats allocator select) count first last) :
    ∃events,last.history=first.history++events := by
  induction trace with
  | nil state => exact ⟨[],(List.append_nil _).symm⟩
  | next step tail ih =>
    obtain ⟨head,firstEq⟩ := tick_history memory floats allocator select _ _ step
    dsimp only [outputHistory] at firstEq
    obtain ⟨more,lastEq⟩ := ih
    exact ⟨head++more,by rw [lastEq,firstEq,List.append_assoc]⟩

/-- Ordinary driver returns expose the same expanded history as their actual
finite tick trace, including nested call/return observations. -/
theorem returned_history {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (select : Selector) {count : Nat} {first : State M} {answer : Outcome M}
    (trace : Interp.NormalTrace (tick memory floats allocator select) count first answer) :
    ∃events,answer.history=first.history++events := by
  induction trace with
  | done step => exact tick_history memory floats allocator select _ _ step
  | next step tail ih =>
    obtain ⟨head,firstEq⟩ := tick_history memory floats allocator select _ _ step
    dsimp only [outputHistory] at firstEq
    obtain ⟨more,lastEq⟩ := ih
    exact ⟨head++more,by rw [lastEq,firstEq,List.append_assoc]⟩

/-- Divergence preserves its two distinct operational possibilities: an actual
finite prefix blocked inside a tick, or one productive infinite combined tick
stream. The local safety interface allows divergence and assumes no universal
normal-return law for host callbacks. -/
theorem divergence_cases {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (Inv : State M → Prop)
    (safe : ∀state,Inv state → tick memory floats allocator select state ⦃ out=>
      match out with | .cont next=>Inv next | .done _=>True ⦄div)
    (state : State M) (held : Inv state) (divergent : run memory floats allocator select state=.div) :
    (∃count last,Interp.ContinuingTrace (tick memory floats allocator select) count state last ∧
      Inv last ∧ tick memory floats allocator select last=.div ∧
      ∃events,last.history=state.history++events) ∨
    (∃states : Nat → State M,states 0=state ∧ ∀n,Inv (states n) ∧
      tick memory floats allocator select (states n)=.ok (.cont (states (n+1))) ∧
      run memory floats allocator select (states n)=.div) := by
  rcases Interp.loop_divergence_open (tick memory floats allocator select) Inv (fun current valid=>WP.dspec_mono (safe current valid) (by intro out post; cases out <;> exact post)) state held divergent with blocked | infinite
  · obtain ⟨count,last,trace,valid,pending⟩ := blocked
    exact Or.inl ⟨count,last,trace,valid,pending,continuing_history memory floats allocator select trace⟩
  · exact Or.inr infinite
end Exec.Theorems.OpenReentrantControl
