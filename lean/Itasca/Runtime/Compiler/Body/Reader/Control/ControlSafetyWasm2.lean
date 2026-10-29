import Itasca.Runtime.Compiler.Body.Relations.Calls.ControlCallbackReady
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterSafety
import Itasca.Runtime.Compiler.Body.Reader.Control.CloseSafety
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchSafety
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnSafety

/-!
Normal return of structured control reader dispatch.

Main declarations: `StructuredReaderCompilerStateWasm2.control_total`. A direct consumer is `Compiler.Body.Reader.Replay.ReachedSafety`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000

theorem StructuredReaderCompilerStateWasm2.control_total {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial compiler types functions returns locals
      data env sourceLocals index ft st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (ctx : code.Context) (opcode : U8) (covered : opcode.val ∈ [2,3,4,5,11,12,13,15])
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (observed : ObservedStack compiler st.core.vals.val)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with core := {st.core with pos := next}} data env ctx index .Wasm2 opcode compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  let pending := state.boundary.pending next advance inbounds
  have ready := state.compiled.control_ready data.length next.val state.boundary.source_bound
    (by omega) (by omega) bodyBound
  have bounded : st.core.pos.val ≤ limits.MAX_MODULE_BYTES.val :=
    (by omega : st.core.pos.val ≤ data.length).trans state.boundary.source_bound
  have frameCount : compiler.frames.val.length = st.blocks.val.length := by
    simpa using state.frames_length
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h
  · have equal : opcode = 2#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_block]
    exact compiler_enter_reader_total ops law compiler pending .block (.inl rfl) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 3#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_loop]
    exact compiler_enter_reader_total ops law compiler pending .loop (.inr (.inl rfl)) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 4#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_if]
    exact compiler_enter_reader_total ops law compiler pending .then_ (.inr (.inr rfl)) signatures observed
      ready.emittedCoordinate (by have := ready.pc; omega) (by have := ready.code; omega)
      (by have := ready.sources; omega) ready.maps ready.frames
  · have equal : opcode = 5#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_else]
    exact state.compiled.close_reader_total ops law bounded _ env true
      pending.opened.shape.core pending.opened.shape.aligned fixups ready.coordinate ready.emittedCoordinate
  · have equal : opcode = 11#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_end]
    exact state.compiled.close_reader_total ops law bounded _ env false
      pending.opened.shape.core pending.opened.shape.aligned fixups ready.coordinate ready.emittedCoordinate
  · have equal : opcode = 12#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_br]
    exact compiler_branch_reader_total ops law compiler _ data env false pending.opened.shape.core
      pending.opened.shape.aligned frameCount fixups ready.pc ready.code ready.sources ready.emittedCoordinate
  · have equal : opcode = 13#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_br_if]
    exact compiler_branch_reader_total ops law compiler _ data env true pending.opened.shape.core
      pending.opened.shape.aligned frameCount fixups ready.pc ready.code ready.sources ready.emittedCoordinate
  · have equal : opcode = 15#u8 := UScalar.eq_of_val_eq h
    subst opcode
    rw [Wasm2.CallbackTrace.dispatch_return]
    exact compiler_return_reader_wasm2_total ops law compiler _ env index pending.opened.shape.core
      (fun _ => ready.nonempty) (by have := ready.code; omega) (by have := ready.sources; omega) ready.emittedCoordinate
end Itasca.Runtime.Code
