import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement

/-!
Lift available Wasm 2 scalar dispatch through its actual profile capacity guard, including extension and SIMD dispatch.

Main declarations: `profile_scalar_available_wasm2` and `profile_base_available_wasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.ReachedNumericAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Lift available Wasm 2 scalar dispatch through its actual profile capacity
guard, including extension and SIMD dispatch. -/
theorem profile_scalar_available_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) (before : V) (post : V → Prop)
    (capacity : st.core.vals.val.length < Usize.max)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (accepted : code.step_wasm2 visitor st.core data env ctx opcode before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄) :
    code.step_profile visitor st data env ctx index .Wasm2 opcode before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = {core := out} ∧ post result.2.2 ⦄ := by
  rw [profile_scalar_eq visitor st data env ctx index opcode before ordinary]
  have notFull : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by
    intro full
    have same := congrArg UScalar.val full
    change st.core.vals.val.length = Usize.max at same
    omega
  rw [if_neg notFull]
  obtain ⟨⟨reply,state,after⟩,called,ok,same,held⟩ := WP.spec_imp_exists accepted
  dsimp only at ok same held
  subst reply state
  rw [called]
  simpa [core.result.Result.Insts.CoreOpsTry.branch] using held

/-- Acceptance of the actual scalar reader lifts through the Wasm 2 profile
capacity guard and source-context adapter. Only the locals are consulted by
ordinary base instructions. -/
theorem profile_base_available_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx sourceCtx : code.Context) (index : U32) (opcode : U8) (before : V) (post : V → Prop)
    (capacity : st.core.vals.val.length < Usize.max)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (base : opcode.val ∉ [28,37,38,208,209,210,252,253])
    (sign : Wasm2.NumericExtensions.signMeaning opcode = none)
    (misc : opcode ≠ code.OP_MISC_PREFIX) (locals : ctx.locals = sourceCtx.locals)
    (accepted : code.step visitor st.core data env sourceCtx opcode before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄) :
    code.step_profile visitor st data env ctx index .Wasm2 opcode before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = {core := out} ∧ post result.2.2 ⦄ := by
  rw [profile_scalar_eq visitor st data env ctx index opcode before ordinary]
  have notFull : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by
    intro full
    have same := congrArg UScalar.val full
    change st.core.vals.val.length = Usize.max at same
    omega
  rw [if_neg notFull,code.step_wasm2.base _ _ _ _ _ _ _ base,
    code.step_extended.base _ _ _ _ _ _ _ sign misc,
    Wasm2.scalar_context _ _ _ _ ctx sourceCtx _ _ ordinary locals]
  obtain ⟨⟨reply,state,after⟩,called,ok,same,held⟩ := WP.spec_imp_exists accepted
  dsimp only at ok same held
  subst reply state
  rw [called]
  simpa [core.result.Result.Insts.CoreOpsTry.branch] using held

end Itasca.Runtime.Code
