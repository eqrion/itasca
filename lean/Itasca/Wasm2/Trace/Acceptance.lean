import Itasca.Wasm2.Trace.BytesDispatch
import Itasca.Wasm2.Trace.ControlRecords
import Itasca.Wasm2.Trace.BytesScalar
import Itasca.Wasm2.Trace.TableBytes
import Itasca.Wasm2.Visitor.ReachedTableLoop

/-!
Sections, each formerly its own module: Step, Correspondence, Acceptance.
-/

/-! ## Step -/

section

/-!
# Step-level callback byte provenance

`steps` shows that the extracted `code.step_profile` satisfies `StepContract`: every
ordinary return has an exact independent callback byte trace, without a total-visitor premise.
`step_contract_of_table` assembles the scalar, control and non-control leaf traces once the
`br_table` case is supplied.
-/

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackTrace
open VisitorTrace

/-- Factors the capacity-guarded scalar arm of `code.step_profile` without changing error
outcomes. -/
theorem dispatch_scalar {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) (v : V)
    (hscalar : opcode.val ∉ controlOpcodes) :
    code.step_profile visitor st data env ctx index opcode v =
      if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
        .ok (.Err .StackTooLarge, st, v)
      else (do
        let (r, s, v') ← code.step_wasm2 visitor st.core data env ctx opcode v
        .ok (r, {st with core := s}, v')) := by
  unfold code.step_profile
  split
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_8 | h_9 | h_10 | h_11 =>
    exact False.elim (hscalar (by decide))
  case h_12 =>
    dsimp only
    split
    · rfl
    · congr 1
      funext pair
      obtain ⟨r, s, v'⟩ := pair
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem step_scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (byte : data.val[p.start.val]'p.inbounds = opcode) :
    ProfileStepRecords p visitor observe ctx opcode := by
  intro v result final v' run
  rw [dispatch_scalar _ _ _ _ _ _ _ _ hscalar] at run
  split at run
  · simp only [Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (.empty _)⟩
  · rename_i capacity
    have size : st.core.vals.val.length < Usize.max := by scalar_tac
    obtain ⟨⟨r, s, w⟩, hr, tail⟩ := ResultFacts.bind_ok_inv _ _ _ run
    simp only [Std.uncurry, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact CallbackBytes.wasm2_scalar p visitor observe records ctx hlocals opcode hscalar size byte
      v r s w hr

/-- Assemble every concrete step once the branch-table protocol is supplied. -/
theorem step_contract_of_table {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (ctx : code.Context) (index : U32) (hlocals : ctx.locals = locals)
    (table : ∀ st (p : Pending data env locals index st),
      data.val[p.start.val]'p.inbounds = 0x0e#u8 →
      ProfileStepRecords p visitor observe ctx 0x0e#u8) :
    StepContract visitor observe data env locals ctx index := by
  intro st p v result out v' run
  let opcode := data.val[p.start.val]'p.inbounds
  have byte : data.val[p.start.val]'p.inbounds = opcode := rfl
  change code.step_profile visitor st data env ctx index opcode v = _ at run
  by_cases hs : opcode.val ∉ controlOpcodes
  · exact step_scalar p visitor observe records ctx hlocals opcode hs byte v result out v' run
  · have hm := Classical.not_not.mp hs
    obtain ⟨⟨n, hn⟩⟩ := opcode
    change n ∈ controlOpcodes at hm
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h <;> subst n
    · exact step_block p visitor observe records ctx byte v result out v' run
    · exact step_loop p visitor observe records ctx byte v result out v' run
    · exact step_if p visitor observe records ctx byte v result out v' run
    · exact step_else p visitor observe records ctx byte v result out v' run
    · exact step_end p visitor observe records ctx byte v result out v' run
    · exact step_br p visitor observe records ctx byte v result out v' run
    · exact step_br_if p visitor observe records ctx byte v result out v' run
    · exact table st p byte v result out v' run
    · exact step_return p visitor observe records ctx byte v result out v' run
    · exact step_call p visitor observe records ctx byte v result out v' run
    · exact step_call_indirect p visitor observe records ctx byte v result out v' run

/-- The full extracted Wasm 2.0 dispatcher satisfies independent callback byte
provenance for every ordinary return, without a total-visitor premise. -/
theorem steps {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (ctx : code.Context) (index : U32) (hlocals : ctx.locals = locals) :
    StepContract visitor observe data env locals ctx index := by
  exact step_contract_of_table visitor observe records data env locals ctx index hlocals
    (fun _ p byte => step_br_table p visitor observe records ctx byte)

end Itasca.Wasm2.CallbackTrace

end

/-! ## Correspondence -/

section

/-!
# Callback traces of body validation

Trace results for `code.validate_body_with`. `body_trace` gives exact byte provenance for
every ordinary return, `body_trace_sound` shows that accepted callbacks spell an independently
encoded, SpecTec-typed body (`AcceptedBody`), and `body_trace_complete` shows that every such body
forces the complete callback sequence. `instrument_body_trace` and `recorder_body_total` show that
instrumenting a visitor or running the recorder yields these traces without changing the
validation result. `Itasca/Results/Trace` states them as public results.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.CallbackTrace

open VisitorTrace

/-- The accepted callbacks spell the same independently encoded and SpecTec-typed body, with
indexed block signatures and declared references. -/
def AcceptedBody (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (observations : List Observation) : Prop :=
  AllAccepted observations ∧ ∃ ft tokens ops next,
    env.types.val[index.val]? = some ft ∧
    Completed data 0#usize observations tokens next ∧ next.val = data.length ∧
    BodyTokens tokens ops ∧ FunctionTyped env ctx.locals ft ops ∧
    DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops

end Itasca.Wasm2.CallbackTrace

namespace Itasca

open VisitorTrace

/-- Every ordinary body return has exact callback byte provenance. A rejected final table may be
partial; an observed rejecting callback is the last one recorded. No valid-input or total-callback
premise is needed. -/
theorem Wasm2.CallbackTrace.body_trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (v v' : V) (result : BodyResult)
    (run : code.validate_body_with visitor data env ctx index v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize observations result :=
  code.validate_body_with.trace_of_contract visitor observe data env ctx index
    (Wasm2.CallbackTrace.steps visitor observe records data env ctx.locals ctx index rfl)
    v v' result run

/-- Accepted callback syntax and generated typing refer to the same body, by uniqueness of the
independent byte grammar. -/
theorem Wasm2.CallbackTrace.body_trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (v v' : V)
    (run : code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.AcceptedBody data env ctx index observations := by
  obtain ⟨observations, log, trace⟩ := Wasm2.CallbackTrace.body_trace
    visitor observe records data env ctx index v v' (.Ok ()) run
  obtain ⟨accepted, tokens, next, chunks, endpos⟩ := trace.accepted
  obtain ⟨ft, ops, entry, ⟨tokens', next', bytes, endpos', hsyntax⟩, typed, declared⟩ :=
    code.validate_body_with.sound visitor data env ctx index v v' run
  have equal_pos : next' = next := UScalar.eq_of_val_eq (endpos'.trans endpos.symm)
  subst next'
  have equal_tokens := chunks.encoded.unique bytes
  subst tokens'
  exact ⟨observations, log, accepted, ft, tokens, ops, next, entry, chunks,
    endpos, hsyntax, typed, declared⟩

/-- Independently encoded and typed bodies force a complete callback trace for accepting
recording visitors within the documented resource bounds. -/
theorem Wasm2.CallbackTrace.body_trace_complete {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (accepts : FullVisitor.Accepts visitor) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (environment : Profile.EnvironmentWithinLimits env)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (body : Wasm2.Validated data env ctx.locals index) (v : V) :
    ∃ v' observations,
      code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v') ∧
      observe v' = observe v ++ observations ∧
      Wasm2.CallbackTrace.AcceptedBody data env ctx index observations := by
  obtain ⟨v', run⟩ := code.validate_body_with.complete visitor accepts
    data env ctx index environment size body v
  obtain ⟨observations, log, trace⟩ := Wasm2.CallbackTrace.body_trace_sound
    visitor observe records data env ctx index v v' run
  exact ⟨v', observations, run, log, trace⟩

/-- Instrumenting an ordinary execution does not change its result or underlying visitor state.
The added observations satisfy byte provenance. -/
theorem Wasm2.CallbackTrace.instrument_body_trace {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (v : V)
    (log : List Observation) (result : BodyResult) (v' : V)
    (run : code.validate_body_with visitor data env ctx index v = .ok (result, v')) :
    ∃ added,
      code.validate_body_with (instrument visitor) data env ctx index (v, log) =
        .ok (result, (v', log ++ added)) ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize added result := by
  obtain ⟨added, instrumented⟩ := code.validate_body_with.instrument_forward
    visitor data env ctx index v log result v' run
  obtain ⟨observations, equal_log, trace⟩ := Wasm2.CallbackTrace.body_trace
    (instrument visitor) Prod.snd (instrument_records visitor) data env ctx index
    (v, log) (v', log ++ added) result instrumented
  have equal : added = observations := List.append_cancel_left equal_log
  exact ⟨added, instrumented, equal ▸ trace⟩

/-- The concrete recorder returns a byte-provenance trace on arbitrary input, including malformed
instructions and reserved opcodes. -/
theorem Wasm2.CallbackTrace.recorder_body_total (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) : ∃ result observations,
    code.validate_body_with recorder data env ctx index [] =
      .ok (result, observations) ∧
      Wasm2.CallbackTrace.BodyTrace data 0#usize observations result := by
  obtain ⟨⟨result, observations⟩, run⟩ := code.validate_body_with.total
    recorder VisitorTrace.recorder_total data env ctx index []
  obtain ⟨added, equal_log, trace⟩ := Wasm2.CallbackTrace.body_trace
    recorder id recorder_records data env ctx index [] observations result run
  simp only [id_eq, List.nil_append] at equal_log
  exact ⟨result, observations, run, equal_log ▸ trace⟩

end Itasca

end

/-! ## Acceptance -/

section

/-!
A source-validated control-reader output followed by an available actual callback accepts with that exact source state.

Main declarations: `bodyRun.available_of_read` and `bodyRun.accepted_lift_on`. A direct consumer is `Compiler.Body.Reader.Calls.Acceptance`.
-/

namespace Itasca.Wasm2.CallbackTrace
open Aeneas Aeneas.Std VisitorTrace

/-- The actual control-reader dispatcher reveals its decoded callback argument. -/
theorem bodyRun.accepted {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (action : A → Action)
    (before after : V) (out : code.BodyState)
    (accepted : bodyRun read visitor action before = .ok (.Ok (), out, after)) :
    ∃ value, read = .ok (.Ok value, out) ∧
      invoke visitor before (.op out.core (action value)) = .ok (.Ok (), after) := by
  unfold bodyRun at accepted
  obtain ⟨⟨result, state⟩, readEq, rest⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
  simp only [Std.uncurry] at rest
  cases result with
  | Err error => simp at rest
  | Ok value =>
    obtain ⟨⟨reply, final⟩, callback, tail⟩ := ResultFacts.bind_ok_inv _ _ _ rest
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error => simp [hookResult] at tail
    | Ok acceptedUnit =>
      cases acceptedUnit
      simp only [hookResult, Result.ok.injEq, Prod.mk.injEq, true_and] at tail
      obtain ⟨rfl, rfl⟩ := tail
      exact ⟨value, readEq, callback⟩

/-- A source-validated control-reader output followed by an available actual
callback accepts with that exact source state. -/
theorem bodyRun.available_of_read {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (action : A → Action) (before : V)
    (value : A) (final : code.BodyState) (post : V → Prop)
    (readCalled : read = .ok (.Ok value,final))
    (accepts : invoke visitor before (.op final.core (action value)) ⦃ result =>
      result.1 = .Ok () ∧ post result.2 ⦄) :
    bodyRun read visitor action before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = final ∧ post result.2.2 ⦄ := by
  obtain ⟨⟨reply,after⟩,called,accepted,held⟩ := WP.spec_imp_exists accepts
  dsimp only at accepted held
  subst reply
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),final,after),?_,rfl,rfl,held⟩
  simp [bodyRun,readCalled,called,hookResult]

/-- Replay the actual metadata-producing Wasm 2 control reader. Only its
independently accepted output invokes the target callback; unrelated visitor
states and unrelated metadata do not need to accept. -/
theorem bodyRun.accepted_lift_on {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.BodyState))
    (source : code.OpVisitor V) (target : code.OpVisitor W) (action : A → Action)
    (before after : V) (compiler : W) (final : code.BodyState) (post : W → Prop)
    (reference : bodyRun read source action before = .ok (.Ok (),final,after))
    (accepts : ∀ value, read = .ok (.Ok value,final) →
      invoke source before (.op final.core (action value)) = .ok (.Ok (),after) →
      invoke target compiler (.op final.core (action value)) ⦃ result => result.1 = .Ok () ∧ post result.2 ⦄) :
    bodyRun read target action compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = final ∧ post result.2.2 ⦄ := by
  obtain ⟨value,readCalled,sourceCalled⟩ := bodyRun.accepted _ _ _ _ _ _ reference
  exact bodyRun.available_of_read read target action compiler value final post readCalled
    (accepts value readCalled sourceCalled)

end Itasca.Wasm2.CallbackTrace

end
