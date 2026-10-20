import Exec.Code.Body.Reader.Common.ReaderProfile

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The Wasm 1 profile only packages the common raw reader state. -/
theorem profile_raw_success_wasm1 {V : Type} (source : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (reference : code.step_profile source st data env ctx index .Wasm1 opcode before = .ok (.Ok (),out,after)) :
    code.step source st.core data env ctx opcode before = .ok (.Ok (),out.core,after) := by
  unfold code.step_profile at reference
  obtain ⟨⟨reply,state,changed⟩,called,rest⟩ := ResultFacts.bind_ok_inv _ _ _ reference
  simp only [Std.uncurry,Result.ok.injEq,Prod.mk.injEq] at rest
  obtain ⟨replyEq,states,changedEq⟩ := rest
  rw [replyEq,changedEq] at called
  have same := congrArg code.BodyState.core states
  dsimp only at same
  simpa only [same] using called

/-- Actual raw acceptance lifts through the profile's exact state adapter. -/
theorem profile_raw_available_wasm1 {W : Type} (target : code.OpVisitor W)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (compiler : W) (post : W → Prop)
    (acceptance : code.step target st.core data env ctx opcode compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out.core ∧ post result.2.2 ⦄) :
    code.step_profile target st data env ctx index .Wasm1 opcode compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄ := by
  obtain ⟨⟨reply,state,after⟩,called,ok,same,held⟩ := WP.spec_imp_exists acceptance
  dsimp only at ok same held
  subst reply state
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),out,after),?_,rfl,rfl,held⟩
  cases out
  simp [code.step_profile,called]

end Exec.Code
