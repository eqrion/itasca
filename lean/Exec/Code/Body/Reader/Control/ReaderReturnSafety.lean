import Exec.Code.Body.Reader.Common.ReaderSafety
import Exec.Code.Body.Reader.Common.ReaderBodySafety
import Itasca.Wasm2.Trace.ControlRecords
import Exec.Code.Local.Relations.Common.TerminalSafety
import Exec.Code.Body.Relations.Control.ReachedControlSafety
import Itasca.Wasm2.Control.Total
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem compiler_return_reader_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (env : module.Env) (index : U32) (shape : Control.Shape state.core)
    (bodyFrame : compiler.reachable = true → 0 < compiler.frames.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    Wasm2.CallbackTrace.bodyRun (Wasm2.returnStep state env index)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (fun _ => .return_) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (Wasm2.CallbackTrace.return_position state env index shape) (by simp)
  · intro out value read
    exact compiler_on_return_total ops law compiler out.core bodyFrame codeFits sourceFits coordinate
end Exec.Code
