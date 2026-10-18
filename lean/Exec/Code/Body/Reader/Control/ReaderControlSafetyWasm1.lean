import Exec.Code.Body.Relations.Calls.ControlCallbackReady
import Exec.Code.Body.Reader.Common.ReaderEnterSafetyWasm1
import Exec.Code.Body.Reader.Common.ReaderCloseSafetyWasm1
import Exec.Code.Body.Reader.Control.ReaderBranchSafetyWasm1
import Exec.Code.Body.Reader.Control.ReaderReturnSafety
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000

theorem StructuredReaderCompilerStateWithTablesWasm1.control_total {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial compiler types functions returns locals
      data env ctx bodyBt st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val+1) (inbounds : st.pos.val < data.length)
    (opcode : U8) (covered : opcode.val ∈ [2,3,4,5,11,12,13,15])
    (observed : ObservedStack compiler st.vals.val)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  let pending := state.boundary.pending next advance inbounds
  have ready := state.compiled.control_ready data.length next.val state.boundary.source_bound
    (by omega) (by omega) bodyBound
  have bounded : st.pos.val ≤ limits.MAX_MODULE_BYTES.val :=
    (by omega : st.pos.val ≤ data.length).trans state.boundary.source_bound
  have frameCount : compiler.frames.val.length = st.ctrls.val.length := state.frames_length
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h
  · have equal : opcode = code.OP_BLOCK := UScalar.eq_of_val_eq (by simpa [global_simps] using h)
    subst opcode
    rw [OpDispatch.dispatch_block]
    exact compiler_block_reader_wasm1_total ops law compiler pending observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = code.OP_LOOP := UScalar.eq_of_val_eq (by simpa [global_simps] using h)
    subst opcode
    rw [OpDispatch.dispatch_loop]
    exact compiler_loop_reader_wasm1_total ops law compiler pending observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = code.OP_IF := UScalar.eq_of_val_eq (by simpa [global_simps] using h)
    subst opcode
    rw [OpDispatch.dispatch_if]
    exact compiler_if_reader_wasm1_total ops law compiler pending observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = code.OP_ELSE := UScalar.eq_of_val_eq (by simpa [global_simps] using h)
    subst opcode
    rw [OpDispatch.dispatch_else]
    exact state.compiled.else_reader_wasm1_total ops law bounded pending fixups ready.emittedCoordinate
  · have equal : opcode = code.OP_END := UScalar.eq_of_val_eq (by simpa [global_simps] using h)
    subst opcode
    rw [OpDispatch.dispatch_end]
    exact state.compiled.end_reader_wasm1_total ops law bounded pending ready.coordinate ready.emittedCoordinate
  · have equal : opcode = code.OP_BR := UScalar.eq_of_val_eq (by simpa [global_simps] using h)
    subst opcode
    rw [OpDispatch.dispatch_br]
    exact compiler_branch_reader_wasm1_total ops law compiler pending false
      frameCount fixups ready.pc ready.code ready.sources ready.emittedCoordinate
  · have equal : opcode = code.OP_BR_IF := UScalar.eq_of_val_eq (by simpa [global_simps] using h)
    subst opcode
    rw [OpDispatch.dispatch_br_if]
    exact compiler_branch_reader_wasm1_total ops law compiler pending true
      frameCount fixups ready.pc ready.code ready.sources ready.emittedCoordinate
  · have equal : opcode = code.OP_RETURN := UScalar.eq_of_val_eq (by simpa [global_simps] using h)
    subst opcode
    rw [OpDispatch.dispatch_return]
    exact compiler_return_reader_total ops law compiler _ ctx pending.opened.shape
      (fun _ => ready.nonempty) (by have := ready.code; omega) (by have := ready.sources; omega) ready.emittedCoordinate
end Exec.Code
