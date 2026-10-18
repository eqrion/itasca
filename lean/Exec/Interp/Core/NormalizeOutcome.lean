import Exec.Interp.Core.BoundClosure
import Exec.Interp.Core.Outcome
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.Control.NormalizeCompose
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem ErasedStep.live {before after : Abs.AFrame} (step : ErasedStep before after)
    (s : _root_.store) (ambient : frame) (rest : List Abs.AFrame) (value : val)
    (live : CoreLiveValue ⟨s,ambient,after::rest,[]⟩ value) :
    CoreLiveValue ⟨s,ambient,before::rest,[]⟩ value := by
  rcases live with impossible | ⟨f,member,localMember | operand⟩
  · cases impossible
  · rcases List.mem_cons.mp member with rfl | member
    · cases step <;> exact Or.inr ⟨_,List.mem_cons_self ..,Or.inl localMember⟩
    · exact Or.inr ⟨f,List.mem_cons_of_mem _ member,Or.inl localMember⟩
  · rcases List.mem_cons.mp member with rfl | member
    · cases step with
      | drop f code front discarded =>
        exact Or.inr ⟨_,List.mem_cons_self ..,Or.inr (List.mem_append_left _ operand)⟩
      | _ => exact Or.inr ⟨_,List.mem_cons_self ..,Or.inr operand⟩
    · exact Or.inr ⟨f,List.mem_cons_of_mem _ member,Or.inr operand⟩

theorem ErasedSteps.live {count before after} (steps : ErasedSteps count before after)
    (s : _root_.store) (ambient : frame) (rest : List Abs.AFrame) (value : val)
    (live : CoreLiveValue ⟨s,ambient,after::rest,[]⟩ value) :
    CoreLiveValue ⟨s,ambient,before::rest,[]⟩ value := by
  induction steps with
  | nil => exact live
  | cons step tail ih => exact step.live s ambient rest value (ih live)

theorem CoreStoreMutation.prepend_normalization {M : Type} {view : M → Slice U8}
    {old fresh : runtime.store.Store M} {count before after s ambient rest}
    (chain : ErasedSteps count before after)
    (mutation : CoreStoreMutation view ⟨s,ambient,after::rest,[]⟩ old fresh) :
    CoreStoreMutation view ⟨s,ambient,before::rest,[]⟩ old fresh := by
  cases mutation with
  | unchanged => exact .unchanged
  | memory issued mutation => exact .memory issued mutation
  | global live wellFormed mutation => exact .global (chain.live s ambient rest _ live) wellFormed mutation

theorem CoreAdvance.prepend_normalization {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {expected : List valtype} {codeLength pc : Nat}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    (advance : CoreAdvance view code store exec expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩) :
    CoreAdvance view code store exec expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambientEq,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.prepend_normalization chain s ambient rest typed,
    fun bound owned => ownership bound (chain.ownership.state owned),ambientEq,fun bound h => bounded bound (chain.codeBound h)⟩

theorem CoreFailure.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {error : runtime.ExecError}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s, ambient, before :: rest, []⟩)
    (failure : CoreFailure allocator hooks exec store platform ⟨s, ambient, middle :: rest, []⟩ error) :
    CoreFailure allocator hooks exec store platform ⟨s, ambient, before :: rest, []⟩ error := by
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

theorem CoreOutcome.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {expected : List valtype}
    {codeLength pc count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    (outcome : CoreOutcome allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩ out) :
    CoreOutcome allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ out := by
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
