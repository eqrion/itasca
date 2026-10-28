import Exec.Code.Local.Capacity.BodyReplay
import Exec.Code.Local.Demand.IndependentBodyDemand

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent body validity constructs its reference run internally, then
replays only its reached steps. The remaining compiler-specific obligation is
the local resource/prefix refinement; an accepted callback trace or successful
target body is not an input to this theorem. -/
theorem independent_body_accepted_replay {W : Type} (target : code.OpVisitor W)
    (profile : ValidationProfile) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (limits : Profile.EnvironmentWithinLimits env)
    (size : data.length ≤ Itasca.limits.MAX_FUNCTION_BYTES.val)
    (body : Profile.Body profile data env ctx.locals index)
    (related : code.BodyState → List Observation → W → Prop) (before : W)
    (initial : ∀ st, code.initial_state env index = .ok (.Ok st) →
      related st [] before)
    (steps : ReachedBody.AcceptingSuffixRefinement recorder target data env ctx index profile (independentBodyLog data env ctx index) related) :
    code.validate_body_with target data env ctx index profile before ⦃ result => result.1 = .Ok () ∧
      ∃ closed, related closed (independentBodyLog data env ctx index) result.2 ∧
        closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  have reference := independentBodyLog.of_valid profile data env ctx index limits size body
  exact code.validate_body_with.accepted_suffix_replay_on recorder target data env ctx index profile
    related (independentBodyLog data env ctx index)
    steps [] before initial reference

end Itasca.Runtime.Code
