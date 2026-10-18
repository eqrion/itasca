import Exec.Code.Body.Reader.Common.ReaderCloseWasm2
import Exec.Code.Body.Reader.Common.ReaderCloseWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_end_root_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {kind bt out}
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
    (p : Wasm2.Pending data env locals index st) {V} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (single : st.blocks.val.length = 1)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0b#u8 before =
      .ok (.Ok (),out,after)) : out.core.ctrls.val = [] := by
  rw [Wasm2.CallbackTrace.dispatch_end] at accepted
  obtain ⟨pair,read,_⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact reader_end_root_wasm2 p single read

theorem reader_end_root_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {kind bt out}
    (single : st.ctrls.val.length = 1)
    (read : code.read_end st = .ok (.Ok (kind,bt),out)) : out.ctrls.val = [] := by
  obtain ⟨C,outer,spine,header,base,typed,controls,values⟩ := p.opened
  have parents : p.parents = [] := by
    have count := congrArg List.length controls
    simp only [List.length_append,List.length_map,List.length_singleton] at count
    exact List.eq_nil_of_length_eq_zero (by omega)
  have effect := code.read_end.realizes st (p.parents.map Wasm1.Frames.Saved.ctrl) p.current.ctrl
    outer p.current.vals controls values base (Nat.le_of_lt p.val_capacity)
  rw [read,WP.spec_ok] at effect
  have controlEq := effect.2.2.2.1
  simpa [parents] using controlEq
end Exec.Code
