import Itasca.Wasm2.Trace.BytesDispatch
import Itasca.Wasm2.Trace.ControlRecords
import Itasca.Wasm2.Trace.Body
import Itasca.Wasm2.Trace.TableBytes

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
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) (opcode : U8) (v : V)
    (hcheck : code.check_opcode profile opcode = .ok (.Ok ()))
    (hscalar : opcode.val ∉ controlOpcodes) :
    code.step_profile visitor st data env ctx index profile opcode v =
      if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
        .ok (.Err .StackTooLarge, st, v)
      else (do
        let (r, s, v') ← code.step_wasm2 visitor st.core data env ctx opcode v
        .ok (r, {st with core := s}, v')) := by
  unfold code.step_profile
  have hok : core.result.Result.Insts.CoreOpsTry.branch
      (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
  rw [hcheck]
  simp only [bind_ok]
  rw [hok]
  simp only [bind_ok]
  split
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_8 | h_9 | h_10 | h_11 =>
    exact False.elim (hscalar (by decide))
  case h_12 =>
    split
    · rfl
    · congr 1
      funext pair
      obtain ⟨r, s, v'⟩ := pair
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem step_scalar {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (byte : data.val[p.start.val]'p.inbounds = opcode) :
    ProfileStepRecords p visitor observe ctx opcode := by
  intro v result final v' run
  rw [dispatch_scalar _ _ _ _ _ _ _ _ _ (byte ▸ p.check_opcode) hscalar] at run
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
    (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (ctx : code.Context) (index : U32) (hlocals : ctx.locals = locals)
    (table : ∀ st (p : Pending data env profile locals index st),
      data.val[p.start.val]'p.inbounds = 0x0e#u8 →
      ProfileStepRecords p visitor observe ctx 0x0e#u8) :
    StepContract visitor observe data env profile locals ctx index := by
  intro st p v result out v' run
  let opcode := data.val[p.start.val]'p.inbounds
  have byte : data.val[p.start.val]'p.inbounds = opcode := rfl
  change code.step_profile visitor st data env ctx index profile opcode v = _ at run
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
    (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (ctx : code.Context) (index : U32) (hlocals : ctx.locals = locals) :
    StepContract visitor observe data env profile locals ctx index := by
  exact step_contract_of_table visitor observe records data env profile locals ctx index hlocals
    (fun _ p byte => step_br_table p visitor observe records ctx byte)

end Itasca.Wasm2.CallbackTrace
