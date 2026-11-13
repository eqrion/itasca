import Itasca.Runtime.Compiler.Module.CompileExecutable
import Itasca.Runtime.Compiler.Module.CompileExecutableCapacities

/-!
Module-level compiler correspondence retains exact source ordering, function-local instruction/table certificates, initializers, and decoded frame capacities. Its code premises are syntactic relations, not assumed execution.

Main declarations: `ModuleCodeRel` and `CompilationCertificate`. A direct consumer is `Integration.Compilation.Complete`.
-/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca

/-- Module-level compiler correspondence retains exact source ordering,
function-local instruction/table certificates, initializers, and decoded frame
capacities. Its code premises are syntactic relations, not assumed execution. -/
structure ModuleCodeRel (raw : ModuleBinary.Module)
    (executable : runtime.compiler.ExecutableModule) : Prop where
  metadata : ModuleElaboration.Matches executable.module.env executable.module.tail raw
  accessors : ModuleElaboration.AccessorTypes executable.module.env raw
  functions : Compiler.ExecutableModuleFunctions executable (Compiler.sourceFunctions raw)
  initializers : Compiler.InitializerMappings executable
  capacities : Compiler.ModuleCapacities executable (Compiler.sourceFunctions raw)

/-- The accepted binary and its compiled code share one canonical source module
under the Wasm 2.0 typing and module restrictions. -/
def CompilationCertificate (bytes : Slice U8)
    (executable : runtime.compiler.ExecutableModule) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith Profile.CodeEncoding raw bytes.val ∧
    ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
    Module_ok (ModuleElaboration.moduleOf raw) ∧ ModuleElaboration.Restrictions raw ∧
    ModuleCodeRel raw executable

/-- T1: every actual accepted compilation constructs its source and complete
module code relation under the allocator law. -/
theorem compile_accepted_certificate {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable)) :
    CompilationCertificate bytes executable := by
  obtain ⟨raw,encoded,elaborated,metadata,typed,restrictions,accessors,functions,initializers⟩ :=
    Compiler.compile_executable_functions ops law bytes limits executable accepted
  obtain ⟨other,otherEncoded,_,_,_,_,_,capacities⟩ :=
    Compiler.compile_executable_capacities ops law bytes limits executable accepted
  have same := ModuleBinary.ModuleEncodingWith.unique Profile.code_prefix_unique encoded otherEncoded
  subst other
  exact ⟨raw,encoded,elaborated,typed,restrictions,⟨metadata,accessors,functions,initializers,capacities⟩⟩
end Itasca.Runtime.Integration
