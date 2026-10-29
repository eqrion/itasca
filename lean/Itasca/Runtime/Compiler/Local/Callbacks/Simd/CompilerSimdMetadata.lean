import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem compiler_simd_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' metadata_step accepted using ops, law



end Itasca.Runtime.Compiler
