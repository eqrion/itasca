import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerPatchMetadata

/-!
Compiler metadata retained when entering a scope.

Main declarations: `compiler_enter_stable_result`. A direct consumer is `Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem compiler_enter_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (status, after)) :
    CompilerStable before after := by
  unfold runtime.compiler.control.FunctionCompiler.enter at accepted
  repeat' metadata_step accepted using ops, law
end Itasca.Runtime.Code
