import Itasca.Wasm2.Visitor.BrTable
import Itasca.Wasm2.Step.Visitor
import Itasca.Visitor.StepLift

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Wasm2.Visitor

set_option maxHeartbeats 2000000 in
/-- Accepting hooks preserve successful multi-value steps and the exact
validator state. Scalar steps depend on locals, not the context result vector. -/
theorem step_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (data : Slice U8) (env : module.Env) (ctx ctx' : code.Context)
    (hlocals : ctx.locals = ctx'.locals) (index : U32) (opcode : U8)
    (st final : code.BodyState) (v : V) (w : W) (v' : V)
    (h : code.step_profile visitor st data env ctx index .Wasm2 opcode v =
      .ok (.Ok (), final, v')) :
    ∃ w', code.step_profile replacement st data env ctx' index .Wasm2 opcode w =
      .ok (.Ok (), final, w') := by
  unfold code.step_profile at h ⊢
  conv at h => lhs; whnf
  conv => arg 1; ext w'; lhs; whnf
  split at h
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_10 | h_11 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, s⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok a =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨⟨r, v'⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [code.visit,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok u =>
        simp [code.visit] at h
        obtain ⟨rfl, rfl⟩ := h
        solve
        | (obtain ⟨w', hw⟩ := ha.on_block w s.core a
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_loop w s.core a
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_if w s.core a
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_else w s.core a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_end w s.core a.1 a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_br w s.core a.1 a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_br_if w s.core a.1 a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_call w s.core a
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
        | (obtain ⟨w', hw⟩ := ha.on_call_indirect w s.core a.1 a.2
           refine ⟨w', ?_⟩
           simp [hw, code.visit])
  case h_8 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, s, v'⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      cases u
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨w', hw⟩ := code.branch_table_with.accepted_transfer visitor replacement ha
        st data env v w s v' hs
      exact ⟨w', by simp [hw, core.result.Result.Insts.CoreOpsTry.branch]⟩
  case h_9 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, ois⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨ois', ho, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rw [ho]
      simp only [bind_ok]
      obtain ⟨⟨r, v'⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [code.visit,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok u =>
        simp [code.visit] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨w', hw⟩ := ha.on_return w ois'
        exact ⟨w', by simp [hw, code.visit]⟩
  case h_12 =>
    rename_i _ h2 h3 h4 h5 h11 h12 h13 h14 h15 h16 h17
    have hscalar : opcode.val ∉ controlOpcodes := by
      have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val :=
        fun he => h (UScalar.eq_of_val_eq he)
      simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨neq h2, neq h3, neq h4, neq h5, neq h11, neq h12,
        neq h13, neq h14, neq h15, neq h16, neq h17⟩
    try simp_all only
    split at h
    · simp at h
    · rename_i hcap
      simp only [hcap, if_false]
      obtain ⟨⟨r, ois, v'⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok u =>
        cases u
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨w', hw⟩ := wasm2_transfer visitor replacement ha
          st.core ois data env ctx ctx' opcode v v' w hscalar hlocals hs
        exact ⟨w', by simp [hw, core.result.Result.Insts.CoreOpsTry.branch]⟩

end Itasca.Wasm2.Visitor
