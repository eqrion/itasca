import Itasca.Runtime.Compiler.Local.Capacity.SegmentBound
import Itasca.Runtime.Compiler.Module.CompileSource

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Accepted source bytes supply the binary framing and metadata coherence
needed by the retained initializer's program-counter bound. -/
theorem segment_validated_pc_bound {module function bytes profile}
    (certificate : SegmentProgram module function)
    (validated : Itasca.ModuleSound.Validated bytes module.module profile)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    function.code.length < U32.max := by
  obtain ⟨raw, encoded, _, matched, _⟩ := validated
  have elements := congrArg (fun raw : Itasca.ModuleBinary.Module => raw.elements.length) matched.1
  have datas := congrArg (fun raw : Itasca.ModuleBinary.Module => raw.data.length) matched.1
  apply certificate.pc_bound encoded bounded
  · simpa [Itasca.ModuleElaboration.fromEnv] using elements.symm
  · simpa [Itasca.ModuleElaboration.fromEnv] using datas.symm

/-- No extra runtime limit premise is required for the initializer PC: the
successful public compiler already checked the fixed module-byte cap. -/
theorem segment_compile_pc_bound {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits) (module : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (function : runtime.bytecode.CompiledFunction) (certificate : SegmentProgram module function) :
    function.code.length < U32.max := by
  obtain ⟨validated, _, bounded⟩ := compile_source_validated allocator law bytes profile limits module accepted
  exact segment_validated_pc_bound certificate validated bounded

end Itasca.Runtime.Code
