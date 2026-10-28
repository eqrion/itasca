import Exec.Code.Local.Demand.ObservationDemand
import Exec.Platform.ReturnedLoop
import Itasca.Wasm2.Trace.ControlRefinement

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca VisitorTrace
set_option maxRecDepth 4096

private theorem recorder_retains (prior : List Observation) :
    Refines recorder code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      (fun log (_ : Unit) => ∃ suffix, log = prior ++ suffix) := by
  rintro log unit event reply after ⟨suffix,held⟩ called
  have appended := recorder_records log event reply after called
  dsimp only [id] at appended
  have accepted : reply = .Ok () := by
    simp [recorder] at called
    exact called.1.symm
  subst reply
  obtain ⟨unitAfter,emptyCalled⟩ := accepts_invoke FullVisitor.empty_accepts unit event
  exact ⟨unitAfter,emptyCalled,suffix ++ [⟨event,.Ok ()⟩],by
    rw [appended,held,List.append_assoc]⟩

/-- A recorder prefix is retained by the actual common step for either full
profile, including partial branch tables and ordinary validation errors. -/
theorem source_step_recorded_prefix (prior before after : List Observation)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) (opcode : U8)
    (result : core.result.Result Unit error.OpError)
    (held : ∃ suffix, before = prior ++ suffix)
    (called : code.step_profile recorder st data env ctx index profile opcode before = .ok (result,final,after)) :
    ∃ suffix, after = prior ++ suffix := by
  obtain ⟨_,_,retained⟩ := code.step_profile.refines recorder
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor _ (recorder_retains prior)
    st data env ctx index profile opcode before () held result final after called
  exact retained

/-- Every normal body-loop result retains all observations already recorded.
The proof uses the loop's least fixed point and requires no compiler, source
state geometry, visitor-normality, or body-acceptance assumption. -/
theorem source_body_recorded_prefix (before after : List Observation)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (result : core.result.Result Unit error.OpError)
    (returned : code.body_loop_loop recorder data env ctx index profile before st = .ok (result,after)) :
    ∃ suffix, after = before ++ suffix := by
  apply Platform.loop_returned_invariant
    (fun state : List Observation × code.BodyState =>
      code.body_loop_loop.body recorder data env ctx index profile state.1 state.2)
    (fun state => ∃ suffix, state.1 = before ++ suffix)
    (fun answer => ∃ suffix, answer.2 = before ++ suffix) ?_
    (before,st) ⟨[],by simp⟩ (result,after) returned
  rintro ⟨log,state⟩ cf held called
  unfold code.body_loop_loop.body at called
  simp only [alloc.vec.Vec.is_empty,bind_ok] at called
  split at called
  · split at called <;> simp at called <;> subst cf <;> exact held
  · obtain ⟨read,readCalled,tail⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ called
    cases read with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
      subst cf
      exact held
    | Ok pair =>
      obtain ⟨opcode,next⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at tail
      obtain ⟨⟨reply,out,middle⟩,step,tail⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ tail
      have retained := source_step_recorded_prefix before log middle _ out data env ctx index profile
        opcode reply held step
      cases reply <;>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail <;>
        subst cf <;> exact retained

/-- A callback reached by the independent reference validator is bounded by
the final reference demand. The remaining accepted body is used only to retain
the event in that source log; it supplies no compiler acceptance premise. -/
theorem source_callback_demand (before middle final : List Observation)
    (state : code.OpIterState) (action : Action) (reply : VisitResult)
    (out : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (result : core.result.Result Unit error.OpError)
    (called : invoke recorder before (.op state action) = .ok (reply,middle))
    (tail : code.body_loop_loop recorder data env ctx index profile middle out = .ok (result,final)) :
    state.vals.length ≤ (observationDemand final).operands ∧
    state.ctrls.length ≤ (observationDemand final).controls := by
  have appended := recorder_records before (.op state action) reply middle called
  dsimp only [id] at appended
  obtain ⟨suffix,retained⟩ := source_body_recorded_prefix middle final out data env ctx index profile result tail
  apply observationDemand.recorded_op (prior := before) (suffix := suffix)
  rw [retained,appended,List.append_assoc]
  rfl

end Itasca.Runtime.Code
