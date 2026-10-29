import Itasca.Runtime.Compiler.Body.Reader.Control.CloseWasm2

/-!
Reader and validator steps at the function's outermost end.

Main declarations: `reader_end_root_wasm2` and `step_end_root_wasm2`. A direct consumer is `Compiler.Body.Control.Closing.IndexedAdvanceOrClosed`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_end_root_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {kind bt out}
    (single : st.blocks.val.length = 1)
    (read : code.end_frame_info st env false = .ok (.Ok (kind,bt),out)) :
    out.core.ctrls.val = [] := by
  have erased : code.end_frame st env false = .ok (.Ok (),out) := by
    simp [code.end_frame,read,core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  have parents : p.parents = [] := by
    have count := congrArg List.length blocks
    simp only [List.length_append,List.length_map,List.length_singleton] at count
    exact List.eq_nil_of_length_eq_zero (by omega)
  have effect := code.end_frame.sound st env false
    (p.parents.map Wasm2.Frames.Saved.ctrl) (p.parents.map Wasm2.Frames.Saved.bt)
    p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    controls blocks (by simp) values base header.inputs header.outputs p.opened.shape.core
  rw [erased,WP.spec_ok] at effect
  have controlEq := (effect rfl).2.2.2.1
  simpa [parents] using controlEq

theorem step_end_root_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (single : st.blocks.val.length = 1)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0b#u8 before =
      .ok (.Ok (),out,after)) : out.core.ctrls.val = [] := by
  rw [Wasm2.CallbackTrace.dispatch_end] at accepted
  obtain ⟨pair,read,_⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact reader_end_root_wasm2 p single read

end Itasca.Runtime.Code
