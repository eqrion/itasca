import Itasca.Visitor.InvariantBodyLoop
import Itasca.Profile.BodyExecution

namespace Itasca.CodeEntry
open Aeneas Aeneas.Std

/-- The selected signature index is used by the Wasm 2.0 body reader. The
Wasm 1.0 reader receives the extracted dummy index zero. -/
def bodyTypeIndex : ValidationProfile → U32 → U32
  | .Wasm1, _ => 0#u32
  | .Wasm2, index => index

theorem runBody.total_on {V : Type} (visitor : code.OpVisitor V)
    (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (typeIndex : U32) (v : V)
    (inv : V → code.BodyState → Prop) (post : V → Prop)
    (initialization : code.initial_state env ctx (bodyTypeIndex profile typeIndex) profile ⦃ result =>
      ∀ st, result = .Ok st → inv v st ⦄)
    (steps : ReachedBody.StepTotalOn visitor data env ctx (bodyTypeIndex profile typeIndex) profile inv)
    (closed : ∀ st v, inv v st → st.core.ctrls.val = [] → st.core.pos.val = data.length → post v) :
    runBody visitor profile data env ctx typeIndex v ⦃ out => out.1 = .Ok () → post out.2 ⦄ := by
  have result := code.validate_body_with_profile.total_on visitor data env ctx
    (bodyTypeIndex profile typeIndex) profile inv post v initialization steps closed
  cases profile <;> exact result
end Itasca.CodeEntry
