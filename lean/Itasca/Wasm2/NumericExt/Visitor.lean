import Itasca.Wasm2.NumericExt.Total
import Itasca.Visitor.StepLift

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Visitor

/-- Accepting replacement hooks preserve the state of every successful scalar
extension, including the cursor after a nonminimal prefix encoding. -/
theorem extended_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (opcode : U8) (v : V) (v' : V) (w : W)
    (hscalar : opcode.val ∉ controlOpcodes) (hlocals : ctx.locals = ctx'.locals)
    (h : code.step_extended visitor st data env ctx opcode v = .ok (.Ok (), final, v')) :
    ∃ w', code.step_extended replacement st data env ctx' opcode w = .ok (.Ok (), final, w') := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some op =>
    rw [code.step_extended.sign visitor st data env ctx opcode op v hm] at h
    rw [code.step_extended.sign replacement st data env ctx' opcode op w hm]
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
      (fun _ => ha.visit_sign_extension w final opcode)
  | none =>
    by_cases hp : opcode = code.OP_MISC_PREFIX
    · have he : opcode = 0xFC#u8 := by simpa [global_simps] using hp
      rw [he] at h ⊢
      rw [code.step_extended.prefixed] at h ⊢
      obtain ⟨r, hr⟩ := reader.read_u32_leb.total data st.pos
      simp only [prefixedStep, hr, bind_ok] at h ⊢
      cases r with
      | Err e => simp at h
      | Ok pair =>
        obtain ⟨subopcode, next⟩ := pair
        cases hm : NumericExtensions.saturatingMeaning subopcode with
        | none => simp [hm] at h
        | some op =>
          simp only [hm] at h ⊢
          exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
            (fun _ => ha.visit_saturating w final subopcode)
    · rw [code.step_extended.base visitor st data env ctx opcode v hm hp] at h
      rw [code.step_extended.base replacement st data env ctx' opcode w hm hp]
      have he := code.step.accepted_erase visitor st final data env ctx opcode v v' h
      rw [scalar_context _ _ data env ctx ctx' opcode () hscalar hlocals] at he
      exact code.step.accepted_lift replacement ha st final data env ctx' opcode w he

end Itasca.MultiValue.Visitor
