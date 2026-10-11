import Itasca.MultiValue.SimdTotal
import Itasca.Visitor.CoreVisitor

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Simd

/-- Exact callback factorization of the SIMD prefix dispatcher. -/
def subStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (subopcode : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let sig ← code.simd_signature subopcode
  match sig with
  | some sig =>
    CoreVisitor.run (code.read_simd_signature st sig)
      (fun v s _ => visitor.on_simd v s subopcode) v
  | none =>
    let lane ← code.simd_lane_info subopcode
    match lane with
    | some (ty, count, replace) =>
      CoreVisitor.run (code.read_simd_lane st data ty count replace)
        (fun v s lane => visitor.on_simd_lane v s subopcode lane) v
    | none =>
      let memory ← code.simd_memory_info subopcode
      match memory with
      | some (align, store, count) =>
        if count != 0#u8 then
          CoreVisitor.run (code.read_simd_memory_lane st data env align store count)
            (fun v s a => visitor.on_simd_memory_lane v s subopcode a.1 a.2) v
        else if store then
          CoreVisitor.run (code.read_store st data env .V128 align)
            (fun v s arg => visitor.on_simd_memory v s subopcode arg) v
        else
          CoreVisitor.run (code.read_load st data env .V128 align)
            (fun v s arg => visitor.on_simd_memory v s subopcode arg) v
      | none =>
        match subopcode with
        | 12#uscalar =>
          CoreVisitor.run (code.read_simd_const st data)
            (fun v s a => visitor.on_simd_const v s a.1 a.2) v
        | 13#uscalar =>
          CoreVisitor.run (code.read_simd_shuffle st data)
            (fun v s a => visitor.on_simd_shuffle v s a.1 a.2) v
        | _ => .ok (.Err .UnrecognizedOpcode, st, v)

def prefixStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let r ← reader.read_u32_leb data st.pos
  match r with
  | .Err e => .ok (.Err e, st, v)
  | .Ok (subopcode, next) => subStep visitor {st with pos := next} data env subopcode v

end Itasca.MultiValue.Simd

namespace Itasca

theorem code.step_wasm2.simd {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 0xFD#u8 v = code.step_simd visitor st data env v := rfl

macro "finish_simd_run" : tactic => `(tactic| (
  simp only [CoreVisitor.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨reply, w⟩ := pair
  all_goals cases reply <;> simp [code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
))

theorem code.step_simd.eq_runs {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (v : V) :
    code.step_simd visitor st data env v = MultiValue.Simd.prefixStep visitor st data env v := by
  unfold code.step_simd MultiValue.Simd.prefixStep
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, MultiValue.Simd.subStep]
    congr 1
    funext sig
    cases sig with
    | some sig => finish_simd_run
    | none =>
      simp only
      congr 1
      funext lane
      cases lane with
      | some triple =>
        obtain ⟨ty, count, replace⟩ := triple
        finish_simd_run
      | none =>
        simp only
        congr 1
        funext mem
        cases mem with
        | some triple =>
          obtain ⟨align, store, count⟩ := triple
          simp only
          split
          · finish_simd_run
          · split <;> finish_simd_run
        | none =>
          simp only
          split
          · finish_simd_run
          · finish_simd_run
          · split <;> simp_all

end Itasca
