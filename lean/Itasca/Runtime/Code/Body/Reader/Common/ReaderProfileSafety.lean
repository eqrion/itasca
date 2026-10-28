import Itasca.Runtime.Code.Body.Reader.Common.ReaderProfile
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The actual profile capacity guard is checked before ordinary decoding.
Only the non-full branch needs the corresponding scalar-reader theorem. -/
theorem reader_profile_scalar_reached {V} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before : V) (post : code.OpIterState → V → Prop)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (step : st.core.vals.val.length < Usize.max →
      code.step_wasm2 visitor st.core data env ctx opcode before ⦃ out =>
        out.1 = .Ok () → post out.2.1 out.2.2 ⦄) :
    code.step_profile visitor st data env ctx index .Wasm2 opcode before ⦃ out =>
      out.1 = .Ok () → post out.2.1.core out.2.2 ⦄ := by
  rw [profile_scalar_eq visitor st data env ctx index opcode before ordinary]
  by_cases full : alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX
  · simp [full]
  · rw [if_neg full]
    have capacity : st.core.vals.val.length < Usize.max := by
      have length := st.core.vals.property
      have notFull : st.core.vals.val.length ≠ Usize.max := by
        intro equal
        apply full
        apply (UScalar.eq_equiv _ _).mpr
        simpa [core.num.Usize.MAX] using equal
      omega
    obtain ⟨⟨reply,state,after⟩,run,success⟩ := WP.spec_imp_exists (step capacity)
    rw [run]
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unitValue =>
      cases unitValue
      simpa only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,WP.spec_ok] using success
end Itasca.Runtime.Code
