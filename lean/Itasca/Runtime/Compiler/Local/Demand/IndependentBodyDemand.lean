import Itasca.Visitor.Recording
import Itasca.Runtime.Platform.Laws
import Itasca.Wasm2.Trace.ControlRefinement
import Itasca.Profile.BodyVisitor

/-!
Sections, each formerly its own module: ObservationDemand, RecordedDemand, IndependentBodyDemand.
-/

/-! ## ObservationDemand -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca VisitorTrace

/-- Source-only temporary-storage demand of one validated observation. Compiler
code, emitted slots, and compiler success do not occur in this definition. -/
structure ObservationDemand where
  operands : Nat
  controls : Nat
  locals : Nat

def eventDemand : Event → ObservationDemand
  | .functionStart ctx _ _ _ => ⟨0,0,ctx.locals.length⟩
  | .op state _ => ⟨state.vals.length,state.ctrls.length,0⟩

def ObservationDemand.join (left right : ObservationDemand) : ObservationDemand :=
  ⟨max left.operands right.operands,max left.controls right.controls,max left.locals right.locals⟩

/-- Componentwise maximum of independently validated callback-state sizes.
A complete compiler theorem must construct this reference log using validator
completeness, rather than require an accepted compiler log from its caller. -/
def observationDemand : List Observation → ObservationDemand
  | [] => ⟨0,0,0⟩
  | observation :: rest => (eventDemand observation.event).join (observationDemand rest)

theorem observationDemand.member {log : List Observation} {observation : Observation}
    (member : observation ∈ log) :
    (eventDemand observation.event).operands ≤ (observationDemand log).operands ∧
    (eventDemand observation.event).controls ≤ (observationDemand log).controls ∧
    (eventDemand observation.event).locals ≤ (observationDemand log).locals := by
  induction log with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨Nat.le_max_left _ _,Nat.le_max_left _ _,Nat.le_max_left _ _⟩
    · obtain ⟨values,controls,locals⟩ := ih member
      exact ⟨values.trans (Nat.le_max_right _ _),controls.trans (Nat.le_max_right _ _),
        locals.trans (Nat.le_max_right _ _)⟩

/-- Any source observation retained in the final reference log has bounded
operand and control vectors. An already recorded prefix can be discarded. -/
theorem observationDemand.recorded_op {prior suffix final : List Observation}
    {state : code.OpIterState} {action : Action} {reply : VisitResult}
    (recorded : final = prior ++ ⟨.op state action,reply⟩ :: suffix) :
    state.vals.length ≤ (observationDemand final).operands ∧
    state.ctrls.length ≤ (observationDemand final).controls := by
  have member : (⟨.op state action,reply⟩ : Observation) ∈ final := by
    rw [recorded]
    simp
  exact ⟨(observationDemand.member member).1,(observationDemand.member member).2.1⟩

end Itasca.Runtime.Compiler

end

/-! ## RecordedDemand -/

section

namespace Itasca.Runtime.Compiler
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
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (opcode : U8)
    (result : core.result.Result Unit error.OpError)
    (held : ∃ suffix, before = prior ++ suffix)
    (called : code.step_profile recorder st data env ctx index opcode before = .ok (result,final,after)) :
    ∃ suffix, after = prior ++ suffix := by
  obtain ⟨_,_,retained⟩ := code.step_profile.refines recorder
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor _ (recorder_retains prior)
    st data env ctx index opcode before () held result final after called
  exact retained

/-- Every normal body-loop result retains all observations already recorded.
The proof uses the loop's least fixed point and requires no compiler, source
state geometry, visitor-normality, or body-acceptance assumption. -/
theorem source_body_recorded_prefix (before after : List Observation)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (result : core.result.Result Unit error.OpError)
    (returned : code.body_loop_loop recorder data env ctx index before st = .ok (result,after)) :
    ∃ suffix, after = before ++ suffix := by
  apply Platform.loop_returned_invariant
    (fun state : List Observation × code.BodyState =>
      code.body_loop_loop.body recorder data env ctx index state.1 state.2)
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
      have retained := source_step_recorded_prefix before log middle _ out data env ctx index
        opcode reply held step
      cases reply <;>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail <;>
        subst cf <;> exact retained

/-- A callback reached by the independent reference validator is bounded by
the final reference demand. The remaining accepted body is used only to retain
the event in that source log; it supplies no compiler acceptance premise. -/
theorem source_callback_demand (before middle final : List Observation)
    (state : code.OpIterState) (action : Action) (reply : VisitResult)
    (out : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (result : core.result.Result Unit error.OpError)
    (called : invoke recorder before (.op state action) = .ok (reply,middle))
    (tail : code.body_loop_loop recorder data env ctx index middle out = .ok (result,final)) :
    state.vals.length ≤ (observationDemand final).operands ∧
    state.ctrls.length ≤ (observationDemand final).controls := by
  have appended := recorder_records before (.op state action) reply middle called
  dsimp only [id] at appended
  obtain ⟨suffix,retained⟩ := source_body_recorded_prefix middle final out data env ctx index result tail
  apply observationDemand.recorded_op (prior := before) (suffix := suffix)
  rw [retained,appended,List.append_assoc]
  rfl

end Itasca.Runtime.Compiler

end

/-! ## IndependentBodyDemand -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- A canonical independent validator observation log. Invalid inputs map to
an empty log; valid inputs are proved below to take the successful branch.
This proof-level choice contains no compiler run or compiled artifact. -/
noncomputable def independentBodyLog (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) : List Observation := by
  classical
  exact if successful : ∃ log, code.validate_body_with recorder data env ctx index [] = .ok (.Ok (),log)
    then Classical.choose successful else []

/-- Source stack/control peaks obtained from independent validation. This is a
proof-level demand, not an executable compiler preflight or a bound on bytes
allocated by the embedding allocator. -/
noncomputable def independentBodyDemand (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) : ObservationDemand :=
  observationDemand (independentBodyLog data env ctx index)

/-- All witnesses of successful reference validation give the same log.
Choice of completeness proof therefore cannot change the source demand. -/
theorem independentBodyLog.unique (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (log : List Observation)
    (reference : code.validate_body_with recorder data env ctx index [] = .ok (.Ok (),log)) :
    independentBodyLog data env ctx index = log := by
  classical
  have successful : ∃ log, code.validate_body_with recorder data env ctx index [] = .ok (.Ok (),log) :=
    ⟨log,reference⟩
  unfold independentBodyLog
  rw [dif_pos successful]
  have same := (Classical.choose_spec successful).symm.trans reference
  simpa using same

/-- Independent source typing, encoding, and validator limits
construct the actual successful reference run. No accepted compiler trace or
completed code certificate is a premise. -/
theorem independentBodyLog.of_valid (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32)
    (limits : Profile.EnvironmentWithinLimits env)
    (size : data.length ≤ Itasca.limits.MAX_FUNCTION_BYTES.val)
    (body : Wasm2.Validated data env ctx.locals index) :
    code.validate_body_with recorder data env ctx index [] =
      .ok (.Ok (),independentBodyLog data env ctx index) := by
  obtain ⟨log,called⟩ := code.validate_body_with.profile_complete recorder recorder_accepts data env ctx index []
    limits size body
  rw [independentBodyLog.unique data env ctx index log called]
  exact called

end Itasca.Runtime.Compiler

end
