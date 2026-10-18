import Exec.Interp.Core.NormalizeOutcome
import Exec.Interp.FloatCore.Outcome
namespace Exec.Interp
open Aeneas Aeneas.Std
theorem FloatCoreAdvance.prepend_normalization {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {expected : List valtype} {codeLength pc : Nat}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    (advance : FloatCoreAdvance view code store exec expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩) :
    FloatCoreAdvance view code store exec expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambientEq,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.prepend_normalization chain s ambient rest typed,
    fun bound owned => ownership bound (chain.ownership.state owned),ambientEq,fun bound h => bounded bound (chain.codeBound h)⟩

theorem FloatCoreFailure.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {error : runtime.ExecError}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s, ambient, before :: rest, []⟩)
    (failure : FloatCoreFailure allocator hooks exec store platform ⟨s, ambient, middle :: rest, []⟩ error) :
    FloatCoreFailure allocator hooks exec store platform ⟨s, ambient, before :: rest, []⟩ error := by
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

theorem FloatCoreOutcome.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {expected : List valtype}
    {codeLength pc count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    (outcome : FloatCoreOutcome allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩ out) :
    FloatCoreOutcome allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ out := by
  obtain ⟨mutation,transition⟩ := outcome
  refine ⟨mutation.prepend_normalization chain,?_⟩
  cases status : out.1 with
  | Ok unit =>
    simp only [status] at transition ⊢
    exact transition.prepend_normalization chain typed
  | Err error =>
    simp only [status] at transition ⊢
    exact ⟨transition.1.prepend_normalization chain typed,transition.2⟩
end Exec.Interp
