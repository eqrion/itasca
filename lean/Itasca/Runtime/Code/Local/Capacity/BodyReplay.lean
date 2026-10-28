import Itasca.Runtime.Code.Local.Capacity.ReaderAcceptance
import Itasca.Binary.ReadByte

namespace Itasca
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ReachedBody

/-- A refinement may inspect the independent accepted suffix, for example to
bound the sizes of all remaining source observations. This supplies source
validation evidence only, never an accepted target run. -/
def AcceptingSuffixRefinement {V W : Type} (source : code.OpVisitor V) (target : code.OpVisitor W)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (profile : ValidationProfile) (final : V) (related : code.BodyState → V → W → Prop) : Prop :=
  ∀ st v w, related st v w →
    code.body_loop_loop source data env ctx typeIndex profile v st = .ok (.Ok (),final) →
    st.core.ctrls.val ≠ [] →
    ∀ (inbounds : st.core.pos.val < data.length) (next : Usize), next.val = st.core.pos.val+1 →
    ∀ out middle, code.step_profile source {core := {st.core with pos := next}} data env ctx typeIndex profile
      data.val[st.core.pos.val] v = .ok (.Ok (),out,middle) →
    code.step_profile target {core := {st.core with pos := next}} data env ctx typeIndex profile
      data.val[st.core.pos.val] w ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        related out middle result.2.2 ∧ next.val ≤ out.core.pos.val ⦄
end ReachedBody

/-- Isolate the independently accepted suffix after a reached step. The
byte read and source step are the actual extracted loop operations. -/
theorem code.body_loop_loop.accepted_tail {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (typeIndex : U32) (profile : ValidationProfile) (st out : code.BodyState)
    (before middle final : V) (nonempty : st.core.ctrls.val ≠ [])
    (inbounds : st.core.pos.val < data.length) (next : Usize)
    (advance : next.val = st.core.pos.val+1)
    (called : code.step_profile visitor {core := {st.core with pos := next}} data env ctx typeIndex profile
      data.val[st.core.pos.val] before = .ok (.Ok (),out,middle))
    (reference : code.body_loop_loop visitor data env ctx typeIndex profile before st = .ok (.Ok (),final)) :
    code.body_loop_loop visitor data env ctx typeIndex profile middle out = .ok (.Ok (),final) := by
  obtain ⟨result,read,position,resultEq,positionEq⟩ := WP.spec_imp_exists
    (reader.read_byte.spec data st.core.pos inbounds)
  have same : position = next := UScalar.eq_of_val_eq (by omega)
  subst position
  rw [resultEq] at read
  have nonemptyBool : st.core.ctrls.val.isEmpty = false := by simpa using nonempty
  unfold code.body_loop_loop at reference ⊢
  rw [loop] at reference
  simpa [code.body_loop_loop.body,alloc.vec.Vec.is_empty,nonemptyBool,read,called,
    core.result.Result.Insts.CoreOpsTry.branch,Std.bind_assoc,Std.uncurry] using reference

/-- Replay an independently accepted reference body through reached-state
acceptance proofs. Both complete profiles use this actual common extracted
loop. The theorem assumes neither target body success nor a target trace. -/
theorem code.body_loop_loop.accepted_suffix_replay_on {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (profile : ValidationProfile) (related : code.BodyState → V → W → Prop)
    (final : V)
    (stepRefinement : ReachedBody.AcceptingSuffixRefinement source target data env ctx typeIndex profile final related)
    (st : code.BodyState) (v : V) (w : W) (initial : related st v w)
    (reference : code.body_loop_loop source data env ctx typeIndex profile v st = .ok (.Ok (),final)) :
    code.body_loop_loop target data env ctx typeIndex profile w st ⦃ result =>
      result.1 = .Ok () ∧ ∃ closed, related closed final result.2 ∧
        closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  generalize measure : Usize.max-st.core.pos.val = remaining
  induction remaining using Nat.strong_induction_on generalizing st v w with
  | h remaining ih =>
    have suffix := reference
    unfold code.body_loop_loop at reference ⊢
    rw [loop] at reference ⊢
    simp only [code.body_loop_loop.body,alloc.vec.Vec.is_empty,bind_ok] at reference ⊢
    by_cases empty : st.core.ctrls.val = []
    · simp only [empty,List.isEmpty_nil,↓reduceIte] at reference ⊢
      by_cases finished : st.core.pos = Slice.len data
      · simp [finished] at reference ⊢
        subst final
        exact ⟨st,initial,empty,finished⟩
      · simp [finished] at reference
    · have nonempty : st.core.ctrls.val.isEmpty = false := by simpa using empty
      simp only [nonempty,Bool.false_eq_true,↓reduceIte] at reference ⊢
      by_cases inbounds : st.core.pos.val < data.length
      · obtain ⟨result,read,next,resultEq,advance⟩ := WP.spec_imp_exists
          (reader.read_byte.spec data st.core.pos inbounds)
        rw [resultEq] at read
        rw [read] at reference ⊢
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.bind_assoc,Std.uncurry] at reference ⊢
        obtain ⟨⟨status,out,middle⟩,called,tail⟩ := ResultFacts.bind_ok_inv _ _ _ reference
        cases status with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
        | Ok unit =>
          cases unit
          obtain ⟨⟨status,targetOut,targetAfter⟩,targetCalled,accepted,same,held,progress⟩ := WP.spec_imp_exists
            (stepRefinement st v w initial suffix empty inbounds next advance out middle called)
          dsimp only at accepted same held progress
          subst status targetOut
          rw [targetCalled]
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
          have smaller : Usize.max-out.core.pos.val < remaining := by
            have maximum := out.core.pos.hmax
            scalar_tac
          have tail' : code.body_loop_loop source data env ctx typeIndex profile middle out = .ok (.Ok (),final) := by
            simpa [code.body_loop_loop,code.body_loop_loop.body,alloc.vec.Vec.is_empty,Std.bind_assoc,Std.uncurry,
              core.result.Result.Insts.CoreOpsTry.branch] using tail
          simpa [code.body_loop_loop,code.body_loop_loop.body,alloc.vec.Vec.is_empty,Std.bind_assoc,Std.uncurry,
            core.result.Result.Insts.CoreOpsTry.branch] using
            ih _ smaller out middle targetAfter held tail' rfl
      · rw [reader.read_byte.eof data st.core.pos (by omega)] at reference
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at reference

/-- Lift reached-step acceptance through the actual size check and the shared,
visitor-independent initial-state construction. The reference may be the
validator's accepting recorder; no successful target run is assumed. -/
theorem code.validate_body_with.accepted_suffix_replay_on {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (profile : ValidationProfile) (related : code.BodyState → V → W → Prop)
    (final : V)
    (stepRefinement : ReachedBody.AcceptingSuffixRefinement source target data env ctx typeIndex profile final related)
    (v : V) (w : W)
    (initial : ∀ st, code.initial_state env typeIndex = .ok (.Ok st) → related st v w)
    (reference : code.validate_body_with source data env ctx typeIndex profile v =
      .ok (.Ok (),final)) :
    code.validate_body_with target data env ctx typeIndex profile w ⦃ result =>
      result.1 = .Ok () ∧ ∃ closed, related closed final result.2 ∧
        closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  unfold code.validate_body_with at reference ⊢
  dsimp only at reference ⊢
  split at reference
  · simp at reference
  · rename_i size
    rw [if_neg size]
    obtain ⟨status,started,tail⟩ := ResultFacts.bind_ok_inv _ _ _ reference
    cases status with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok st =>
      rw [started]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      apply code.body_loop_loop.accepted_suffix_replay_on source target data env ctx typeIndex profile related final
        stepRefinement st v w (initial st started)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,code.body_loop] using tail

end Itasca
