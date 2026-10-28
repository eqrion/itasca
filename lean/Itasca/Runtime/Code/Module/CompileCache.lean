import Itasca.Runtime.Code.Module.CompileSemantic

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Canonical accepted environment parsing establishes the exact imported and
defined index-space caches retained by the executable module. -/
theorem CompileWitness.cache_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable) :
    ∃ tables memories, ModuleEnv.Cache w.env tables memories := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  have decoded := module.validate_env_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).moduleModuleVisitorInst
    run.environment run.region w.env run.environmentLength run.decoded run.decode_environment
  have semantic := module.validate_env.profile_semantic_spec run.environment profile
  rw [decoded, WP.spec_ok] at semantic
  obtain ⟨decls, represented, _, _, _, _⟩ := semantic
  exact ⟨decls.tables, decls.memories, represented.cache⟩

theorem CompileWitness.cache {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) :
    ∃ tables memories, ModuleEnv.Cache executable.module.env tables memories := by
  rw [(w.initializers law).1]
  exact w.cache_input

end Itasca.Runtime.Code
