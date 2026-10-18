import Exec.Interp.Machines.Slice.SliceAdvance
import Exec.Interp.Relations.SourceCallCause

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Source traps admitted by the integer/control slice. -/
def SliceTrap (trap : runtime.Trap) : Prop :=
  trap = .Unreachable ∨ trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow

/-- Every slice error has an instruction-level source or boundary witness. -/
def SliceFailure {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (source : Abs.AState)
    (error : runtime.ExecError) : Prop :=
  ((∃ trap, error = .Trap trap ∧ SliceTrap trap) ∧ ∃ n, 0 < n ∧ Spec.StepsHN n (Abs.decode source) []
    ⟨⟨source.store, source.ambient⟩, [.TRAP]⟩) ∨
  (error = .Terminated ∧ ∃ after, hooks.interrupt platform = .ok (.Terminate, after)) ∨
  ∃ index raw inst compiled,
    index.val + 1 = exec.frames.length ∧ exec.frames.val[index.val]? = some raw ∧
    store.instances.val[raw.instance.val]? = some inst ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source error

/-- A normally returned dispatch either advances the retained invariant or
reports an error with a precise trap, interruption, or call-resource cause. -/
def SliceOutcome {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (expected : List valtype)
    (codeLength pc : Nat) (pending : Bool) (source : Abs.AState)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.2.2.1 = store ∧ match out.1 with
  | .Ok _ => SliceAdvance store out.2.1 expected codeLength pc pending source
  | .Err error => SliceFailure allocator hooks exec store platform source error

theorem SliceFailure.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {error : runtime.ExecError}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s, ambient, before :: rest, []⟩)
    (failure : SliceFailure allocator hooks exec store platform ⟨s, ambient, middle :: rest, []⟩ error) :
    SliceFailure allocator hooks exec store platform ⟨s, ambient, before :: rest, []⟩ error := by
  rcases failure with ⟨kind, n, positive, steps⟩ | interrupted | rejected
  · refine Or.inl ⟨kind, ?_⟩
    rcases (chain.sound s ambient rest typed).2 with ⟨_, same⟩ | simulation
    · exact ⟨n, positive, by simpa only [same] using steps⟩
    · rcases simulation with ⟨same, _⟩ | ⟨m, hm, reductions⟩
      · exact ⟨n, positive, by simpa only [same] using steps⟩
      · exact ⟨m + n, by omega, by simpa using reductions.trans steps⟩
  · exact Or.inr (Or.inl interrupted)
  · obtain ⟨index, raw, inst, compiled, last, frameFound, instanceFound, codeFound, cause⟩ := rejected
    refine Or.inr (Or.inr ⟨index, raw, inst, compiled, last, frameFound, instanceFound, codeFound, ?_⟩)
    have counted : ∃ n, Spec.StepsHN n (Abs.decode ⟨s, ambient, before :: rest, []⟩) []
        (Abs.decode ⟨s, ambient, middle :: rest, []⟩) := by
      rcases (chain.sound s ambient rest typed).2 with ⟨_, same⟩ | simulation
      · subst middle
        exact ⟨0, .refl typed.decode_wf⟩
      · rcases simulation with ⟨same, _⟩ | ⟨n, positive, reductions⟩
        · exact ⟨0, by rw [← same]; exact .refl typed.decode_wf⟩
        · exact ⟨n, reductions⟩
    obtain ⟨n, steps⟩ := counted
    exact cause.prepend steps rfl rfl

theorem SliceOutcome.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {expected : List valtype} {codeLength pc : Nat}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s, ambient, before :: rest, []⟩)
    (outcome : SliceOutcome allocator hooks exec store platform expected codeLength pc false
      ⟨s, ambient, middle :: rest, []⟩ out) :
    SliceOutcome allocator hooks exec store platform expected codeLength pc false
      ⟨s, ambient, before :: rest, []⟩ out := by
  obtain ⟨sameStore, transition⟩ := outcome
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok unit =>
    simp only [status] at transition ⊢
    exact transition.prepend_normalization chain typed
  | Err error =>
    simp only [status] at transition ⊢
    exact transition.prepend_normalization chain typed

end Exec.Interp
