import Itasca.Runtime.Code.Body.Reader.Common.ReaderBodySafety
import Itasca.Runtime.Code.Local.Relations.Calls.BranchCallbackSafety
import Itasca.Runtime.Code.Body.Reader.Control.ReaderBranchInfo
import Itasca.Wasm2.Visitor.Total
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_branch_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.BodyState) (data : Slice U8) (env : module.Env) (conditional : Bool)
    (shape : Control.Shape state.core)
    (aligned : state.blocks.val.length = state.core.ctrls.val.length)
    (frames : compiler.frames.val.length = state.blocks.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (pcBound : compiler.function.code.val.length+3 < 2^32)
    (codeFits : compiler.function.code.val.length+3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+3 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CallbackTrace.bodyRun (code.branch_info state data env conditional)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      (fun pair => if conditional then .br_if pair.1 pair.2 else .br pair.1 pair.2) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (code.branch_info.total state data env conditional shape aligned) (by simp)
  · intro out pair read
    obtain ⟨depth,view⟩ := pair
    have selected := reader_branch_info_selected state data env conditional depth view out aligned read
    have bound : depth.val < state.blocks.val.length := by
      by_contra no
      simp [Wasm2.labelAt] at selected
      omega
    have depthFits : depth.val < compiler.frames.val.length := by omega
    cases conditional with
    | false =>
      exact compiler_br_callback_total ops law compiler out.core depth view depthFits fixups
        (by omega) (by omega) coordinate
    | true =>
      exact compiler_br_if_callback_total ops law compiler out.core depth view depthFits fixups
        pcBound codeFits sourceFits coordinate
end Itasca.Runtime.Code
