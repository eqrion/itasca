import Exec.Interp.StructuredMachine.ExecutableCoverage
namespace Exec.Interp.StructuredMachine

/-- Resolve retained-table projections at an actual compiled function. -/
instance executable_stateful_projection (compiled : runtime.bytecode.CompiledFunction) :
    StatefulProjection (Executable.emission compiled) compiled.indirect.val := by
  change StatefulProjection (Code.ExecutableEmission (Code.CompilerTables.ofFunction compiled))
    (Code.CompilerTables.ofFunction compiled).indirect
  infer_instance

instance executable_indirect_projection (compiled : runtime.bytecode.CompiledFunction) :
    IndirectProjection (Executable.emission compiled) compiled.indirect.val := by
  change IndirectProjection (Code.ExecutableEmission (Code.CompilerTables.ofFunction compiled))
    (Code.CompilerTables.ofFunction compiled).indirect
  infer_instance

instance executable_simd_projection (compiled : runtime.bytecode.CompiledFunction) :
    SimdProjection (Executable.emission compiled) compiled.simd.val compiled.v128_pool.val := by
  change SimdProjection (Code.ExecutableEmission (Code.CompilerTables.ofFunction compiled))
    (Code.CompilerTables.ofFunction compiled).simd (Code.CompilerTables.ofFunction compiled).constants
  infer_instance
end Exec.Interp.StructuredMachine
