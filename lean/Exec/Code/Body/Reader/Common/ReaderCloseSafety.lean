import Exec.Code.Body.Reader.Common.ReaderBodySafety
import Exec.Code.Body.Relations.Control.ReachedControlSafety
import Itasca.Wasm2.Visitor.Total
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem StructuredCompilerPrefixWithTables.close_reader_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.BodyState) (env : module.Env) (isElse : Bool)
    (shape : Control.Shape state.core)
    (aligned : state.blocks.val.length = state.core.ctrls.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val+state.core.pos.val ≤ Usize.max)
    (emitCoordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CallbackTrace.bodyRun (code.end_frame_info state env isElse)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      (fun pair => if isElse then .else_ pair.2 else .end_ pair.1 pair.2) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  have effect := code.end_frame_info.total state env isElse shape aligned
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono effect (by simp)
  · intro out pair read
    have data := effect
    rw [read,WP.spec_ok] at data
    dsimp only at data
    obtain ⟨kind,bt⟩ := pair
    cases isElse with
    | false =>
      apply invariant.end_total ops law bounded out.core kind bt _ emitCoordinate
      simpa only [data.2.2.2] using coordinate
    | true => exact invariant.else_total ops law bounded fixups out.core bt emitCoordinate
end Exec.Code
