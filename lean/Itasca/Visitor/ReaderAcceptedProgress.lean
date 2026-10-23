import Itasca.Wasm2.Visitor.Step
import Itasca.Wasm2.Visitor.Total
namespace Itasca
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

/-- The accepted reader advances the concrete cursor even when later bytes are malformed. Only
the reached raw control geometry is needed. -/
theorem code.step_profile.accepted_progress {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (profile : ValidationProfile)
    (st final : code.BodyState) (value after : V)
    (dataBound : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (shape : Control.Shape st.core)
    (blocks : st.blocks.val.length = st.core.ctrls.val.length)
    (controlBound : st.blocks.val.length ≤ st.core.pos.val+1)
    (nonempty : st.core.ctrls.val ≠ []) (inbounds : st.core.pos.val<data.length)
    (next : Usize) (advance : next.val=st.core.pos.val+1)
    (accepted : code.step_profile visitor ⟨{st.core with pos:=next}⟩ data env ctx typeIndex profile
      data.val[st.core.pos.val] value = .ok (.Ok (),final,after)) :
    next.val ≤ final.core.pos.val := by
  obtain ⟨unitValue,erased⟩ := Wasm2.Visitor.step_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
    data env ctx ctx rfl typeIndex profile data.val[st.core.pos.val]
    ⟨{st.core with pos:=next}⟩ final value () after accepted
  cases unitValue
  obtain ⟨result,read,position,equal,positionEq⟩ := WP.spec_imp_exists
    (reader.read_byte.spec data st.core.pos inbounds)
  have same : position=next := UScalar.eq_of_val_eq (by omega)
  subst position
  rw [equal] at read
  have body : code.body_loop_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx typeIndex profile () st = .ok (.cont ((),final)) := by
    have nonemptyBool : st.core.ctrls.val.isEmpty=false := by simpa using nonempty
    simp [code.body_loop_loop.body,alloc.vec.Vec.is_empty,nonemptyBool,read,
      core.result.Result.Insts.CoreOpsTry.branch,erased]
  have checked := code.body_loop_loop.body.total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
    data env ctx typeIndex profile st () dataBound shape blocks controlBound
  rw [body,WP.spec_ok] at checked
  have progress := checked.2
  have bound : final.core.pos.val≤Usize.max := by scalar_tac
  dsimp only at progress
  omega
end Itasca
