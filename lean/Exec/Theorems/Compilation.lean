import Exec.Code.Module.CompileExecutable
import Exec.Code.Module.CompileExecutableCapacities
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca

/-- Module-level compiler correspondence retains exact source ordering,
function-local instruction/table certificates, initializers, and decoded frame
capacities. Its code premises are syntactic relations, not assumed execution. -/
structure ModuleCodeRel (raw : ModuleBinary.Module)
    (executable : runtime.compiler.ExecutableModule) : Prop where
  metadata : ModuleElaboration.Matches executable.module.env executable.module.tail raw
  accessors : ModuleElaboration.AccessorTypes executable.module.env raw
  functions : Code.ExecutableModuleFunctions executable (Code.sourceFunctions raw)
  initializers : Code.InitializerMappings executable
  capacities : Code.ModuleCapacities executable (Code.sourceFunctions raw)

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
    Code.compile_executable_functions ops law bytes profile limits executable accepted
  obtain ⟨other,otherEncoded,_,_,_,_,_,capacities,_⟩ :=
    Code.compile_executable_capacities ops law bytes profile limits executable accepted
  have same := Profile.module_unique encoded otherEncoded
  subst other
  exact ⟨raw,encoded,elaborated,typed,restrictions,⟨metadata,accessors,functions,initializers,capacities⟩,selected⟩
end Exec.Theorems
