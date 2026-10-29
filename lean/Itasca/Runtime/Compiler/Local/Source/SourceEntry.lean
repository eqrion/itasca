import Itasca.Runtime.Compiler.Local.Source.SourceLengths
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_new_sources {A : Type} (ops : runtime.platform.Alloc A)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) :
    runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart ⦃ out =>
      SourceAligned out ⦄ := by
  simp [runtime.compiler.FunctionCompiler.new, WP.spec_ok, SourceAligned]
end Itasca.Runtime.Code
