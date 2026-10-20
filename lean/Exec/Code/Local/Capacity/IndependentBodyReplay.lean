import Exec.Code.Local.Capacity.BodyReplay
import Exec.Code.Local.Demand.IndependentBodyDemand

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Wasm 1's extracted body wrapper uses zero for its unused type-index
argument; Wasm 2 retains the function's actual type index. -/
abbrev bodyValidationIndex (profile : ValidationProfile) (index : U32) : U32 :=
  match profile with | .Wasm1 => 0#u32 | .Wasm2 => index

/-- The actual entry pipeline selects the same common body validator used by
reached-state replay, with its explicit profile-specific index convention. -/
theorem profile_body_run_eq {V : Type} (visitor : code.OpVisitor V)
    (profile : ValidationProfile) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (before : V) :
    CodeEntry.runBody visitor profile data env ctx index before =
      code.validate_body_with_profile visitor data env ctx (bodyValidationIndex profile index) profile before := by
  cases profile <;> rfl

/-- Independent body validity constructs its reference run internally, then
replays only its reached steps. The remaining compiler-specific obligation is
the local resource/prefix refinement; an accepted callback trace or successful
target body is not an input to this theorem. -/
theorem independent_body_accepted_replay {W : Type} (target : code.OpVisitor W)
    (profile : ValidationProfile) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (ft : types.FuncType)
    (signature : env.types.val[index.val]? = some ft) (results : ctx.results.val = ft.results.val)
    (environment : Profile.Environment profile env) (limits : Profile.EnvironmentWithinLimits profile env)
    (size : data.length ≤ Itasca.limits.MAX_FUNCTION_BYTES.val)
    (body : Profile.Body profile data env ctx.locals index)
    (related : code.BodyState → List Observation → W → Prop) (before : W)
    (initial : ∀ st, code.initial_state env ctx (bodyValidationIndex profile index) profile = .ok (.Ok st) →
      related st [] before)
    (steps : ReachedBody.AcceptingSuffixRefinement recorder target data env ctx
      (bodyValidationIndex profile index) profile (independentBodyLog profile data env ctx index) related) :
    CodeEntry.runBody target profile data env ctx index before ⦃ result => result.1 = .Ok () ∧
      ∃ closed, related closed (independentBodyLog profile data env ctx index) result.2 ∧
        closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  have reference := independentBodyLog.of_valid profile data env ctx index ft signature results environment limits size body
  rw [profile_body_run_eq] at reference ⊢
  exact code.validate_body_with_profile.accepted_suffix_replay_on recorder target data env ctx
    (bodyValidationIndex profile index) profile related (independentBodyLog profile data env ctx index)
    steps [] before initial reference

end Exec.Code
