import Itasca.Runtime.Compiler.Local.Demand.ObservationDemand
import Itasca.Profile.BodyVisitor

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- A canonical independent validator observation log. Invalid inputs map to
an empty log; valid inputs are proved below to take the successful branch.
This proof-level choice contains no compiler run or compiled artifact. -/
noncomputable def independentBodyLog (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) : List Observation := by
  classical
  exact if successful : ∃ log, code.validate_body_with recorder data env ctx index .Wasm2 [] = .ok (.Ok (),log)
    then Classical.choose successful else []

/-- Source stack/control peaks obtained from independent validation. This is a
proof-level demand, not an executable compiler preflight or a bound on bytes
allocated by the embedding allocator. -/
noncomputable def independentBodyDemand (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) : ObservationDemand :=
  observationDemand (independentBodyLog data env ctx index)

/-- All witnesses of successful reference validation give the same log.
Choice of completeness proof therefore cannot change the source demand. -/
theorem independentBodyLog.unique (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) (log : List Observation)
    (reference : code.validate_body_with recorder data env ctx index .Wasm2 [] = .ok (.Ok (),log)) :
    independentBodyLog data env ctx index = log := by
  classical
  have successful : ∃ log, code.validate_body_with recorder data env ctx index .Wasm2 [] = .ok (.Ok (),log) :=
    ⟨log,reference⟩
  unfold independentBodyLog
  rw [dif_pos successful]
  have same := (Classical.choose_spec successful).symm.trans reference
  simpa using same

/-- Independent source typing, encoding, profile, and validator limits
construct the actual successful reference run. No accepted compiler trace or
completed code certificate is a premise. Both complete profiles are covered: a valid Wasm 1.0 body
has the same run under both profiles. -/
theorem independentBodyLog.of_valid (profile : ValidationProfile) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32)
    (limits : Profile.EnvironmentWithinLimits env)
    (size : data.length ≤ Itasca.limits.MAX_FUNCTION_BYTES.val)
    (body : Profile.Body profile data env ctx.locals index) :
    code.validate_body_with recorder data env ctx index profile [] =
      .ok (.Ok (),independentBodyLog data env ctx index) := by
  obtain ⟨log,called⟩ := code.validate_body_with.profile_complete recorder recorder_accepts data env ctx index .Wasm2 []
    limits size body.to_wasm2
  rw [independentBodyLog.unique data env ctx index log called]
  cases profile with
  | Wasm1 => exact code.validate_body_with.wasm1_of_body recorder data env ctx index [] _ limits size body called
  | Wasm2 => exact called

end Itasca.Runtime.Code
