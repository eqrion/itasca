import Exec.Code.Local.Demand.ObservationDemand
import Itasca.Profile.BodyVisitor

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- A canonical independent validator observation log. Invalid inputs map to
an empty log; valid inputs are proved below to take the successful branch.
This proof-level choice contains no compiler run or compiled artifact. -/
noncomputable def independentBodyLog (profile : ValidationProfile) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) : List Observation := by
  classical
  exact if successful : ∃ log, CodeEntry.runBody recorder profile data env ctx index [] = .ok (.Ok (),log)
    then Classical.choose successful else []

/-- Source stack/control peaks obtained from independent validation. This is a
proof-level demand, not an executable compiler preflight or a bound on bytes
allocated by the embedding allocator. -/
noncomputable def independentBodyDemand (profile : ValidationProfile) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) : ObservationDemand :=
  observationDemand (independentBodyLog profile data env ctx index)

/-- All witnesses of successful reference validation give the same log.
Choice of completeness proof therefore cannot change the source demand. -/
theorem independentBodyLog.unique (profile : ValidationProfile) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) (log : List Observation)
    (reference : CodeEntry.runBody recorder profile data env ctx index [] = .ok (.Ok (),log)) :
    independentBodyLog profile data env ctx index = log := by
  classical
  have successful : ∃ log, CodeEntry.runBody recorder profile data env ctx index [] = .ok (.Ok (),log) :=
    ⟨log,reference⟩
  unfold independentBodyLog
  rw [dif_pos successful]
  have same := (Classical.choose_spec successful).symm.trans reference
  simpa using same

/-- Independent source typing, encoding, profile, and validator limits
construct the actual successful reference run. No accepted compiler trace or
completed code certificate is a premise. Both complete profiles are covered. -/
theorem independentBodyLog.of_valid (profile : ValidationProfile) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) (ft : types.FuncType)
    (signature : env.types.val[index.val]? = some ft) (results : ctx.results.val = ft.results.val)
    (environment : Profile.Environment profile env) (limits : Profile.EnvironmentWithinLimits profile env)
    (size : data.length ≤ Itasca.limits.MAX_FUNCTION_BYTES.val)
    (body : Profile.Body profile data env ctx.locals index) :
    CodeEntry.runBody recorder profile data env ctx index [] =
      .ok (.Ok (),independentBodyLog profile data env ctx index) := by
  obtain ⟨log,called⟩ := CodeEntry.runBody.complete recorder recorder_accepts profile data env ctx index ft []
    signature results environment limits size body
  rw [independentBodyLog.unique profile data env ctx index log called]
  exact called

/-- Each observation retained by the independently constructed reference has
its vector sizes bounded by that same source-only demand. -/
theorem independentBodyDemand.observed (profile : ValidationProfile) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) (observation : Observation)
    (member : observation ∈ independentBodyLog profile data env ctx index) :
    (eventDemand observation.event).operands ≤ (independentBodyDemand profile data env ctx index).operands ∧
    (eventDemand observation.event).controls ≤ (independentBodyDemand profile data env ctx index).controls ∧
    (eventDemand observation.event).locals ≤ (independentBodyDemand profile data env ctx index).locals :=
  observationDemand.member member

end Exec.Code
