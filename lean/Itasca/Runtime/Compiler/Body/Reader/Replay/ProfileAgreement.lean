import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Visitor.EventDispatch
import Itasca.Visitor.Erasure
import Itasca.Wasm2.Step.Dispatch

/-!
Agreement of shared scalar reader steps across validation profiles.

Main declarations: `profile_scalar_eq` and `profile_base_success_wasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.ProfileAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem profile_scalar_eq {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before : V)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes) :
    code.step_profile visitor st data env ctx index .Wasm2 opcode before =
      (if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
        .ok (.Err .StackTooLarge, st, before)
      else do
        let (reply, state, after) ← code.step_wasm2 visitor st.core data env ctx opcode before
        let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
        match cf with
        | .Continue _ => .ok (.Ok (), {core := state}, after)
        | .Break residual =>
          let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame error.OpError) residual
          .ok (error, {core := state}, after)) := by
  have hok : core.result.Result.Insts.CoreOpsTry.branch
      (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
  simp only [code.step_profile, code.check_opcode, bind_ok, hok]
  split <;> try rfl
  all_goals exact False.elim (ordinary (by decide))

theorem profile_scalar_success {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    st.core.vals.val.length < Usize.max ∧
      code.step_wasm2 visitor st.core data env ctx opcode before = .ok (.Ok (), out.core, after) := by
  rw [profile_scalar_eq visitor st data env ctx index opcode before ordinary] at accepted
  by_cases full : alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX
  · simp [full] at accepted
  · rw [if_neg full] at accepted
    obtain ⟨⟨reply, state, changed⟩, called, tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, Prod.mk.injEq, true_and] at tail
      obtain ⟨rfl, rfl⟩ := tail
      refine ⟨?_, called⟩
      have length := st.core.vals.property
      have notFull : st.core.vals.val.length ≠ Usize.max := by
        intro equal
        apply full
        apply (UScalar.eq_equiv _ _).mpr
        simpa [core.num.Usize.MAX] using equal
      omega

/-- Successful ordinary Wasm 2 dispatch supplies both the reader capacity
and the exact scalar callback run, with the pending zipper's result context. -/
theorem profile_base_success_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx ctx' : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (base : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253])
    (sign : Wasm2.NumericExtensions.signMeaning opcode = none)
    (misc : opcode ≠ code.OP_MISC_PREFIX) (locals : ctx.locals = ctx'.locals)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    st.core.vals.val.length < Usize.max ∧
      code.step visitor st.core data env ctx' opcode before = .ok (.Ok (), out.core, after) := by
  obtain ⟨capacity, run⟩ := profile_scalar_success visitor st out data env ctx index opcode before after ordinary accepted
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base,
    code.step_extended.base _ _ _ _ _ _ _ sign misc,
    Wasm2.scalar_context _ _ _ _ ctx ctx' _ _ ordinary locals] at run
  exact ⟨capacity, run⟩

end Itasca.Runtime.Compiler
