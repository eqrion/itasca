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
in the selected complete profile. -/
def CompilationCertificate (bytes : Slice U8) (profile : ValidationProfile)
    (executable : runtime.compiler.ExecutableModule) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
    ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
    Module_ok (ModuleElaboration.moduleOf raw) ∧ ModuleElaboration.Profile raw profile ∧
    ModuleCodeRel raw executable ∧ executable.profile = profile

/-- T1: every actual accepted compilation constructs its source and complete
module code relation under the allocator law. -/
theorem compile_accepted_certificate {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes profile limits = .ok (.Ok executable)) :
    CompilationCertificate bytes profile executable := by
  obtain ⟨raw,encoded,elaborated,metadata,typed,restrictions,accessors,functions,initializers,selected⟩ :=
    Compiler.compile_executable_functions ops law bytes profile limits executable accepted
  obtain ⟨other,otherEncoded,_,_,_,_,_,capacities,_⟩ :=
    Compiler.compile_executable_capacities ops law bytes profile limits executable accepted
  have same := Profile.module_unique encoded otherEncoded
  subst other
  exact ⟨raw,encoded,elaborated,typed,restrictions,⟨metadata,accessors,functions,initializers,capacities⟩,selected⟩
end Itasca.Runtime.Integration
