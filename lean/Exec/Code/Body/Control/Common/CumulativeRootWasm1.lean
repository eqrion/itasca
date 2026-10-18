import Exec.Code.Body.Control.Common.CumulativePointWasm1
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerRoot
import Exec.Code.Body.Reader.Calls.ReaderControlIndirectWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm1.root_end_final {A : Type}
    (ops : runtime.platform.Alloc A)
    {initial before after final : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st current savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals
      data env ctx bodyBt st [] current [] savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (byte : data.val[st.pos.val]'inbounds = 11#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 11#u8 before = .ok (.Ok (),out,after))
    (rest : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt out after final) :
    final = after := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨_,read,_,_,_,_⟩ := reader_end_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out
    (by simpa only [p, ReaderBoundaryWasm1.pending, global_simps] using byte) (by simpa only [global_simps] using accepted)
  obtain ⟨C,outer,spine,header,base,typed,controls,vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using wasm1_spine_values spine
  have rawEq : st.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have closed : out.ctrls.val = [] := by
    have effect := code.read_end.realizes {st with pos := next} [] savedCurrent.ctrl [] savedCurrent.vals
      (by simpa using controls) (by simp [rawEq]) (by simpa [outerEq] using base)
      (Nat.le_of_lt p.val_capacity)
    rw [read,WP.spec_ok] at effect
    obtain ⟨_,_,_,controls,_⟩ := effect
    exact controls
  exact (rest.closed closed).1
end Exec.Code
