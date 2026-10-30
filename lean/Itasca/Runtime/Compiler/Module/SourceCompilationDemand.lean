import Itasca.Runtime.Compiler.Module.EnvironmentCompilationAvailable
import Itasca.Runtime.Compiler.Module.InitializerCompilationAvailable
import Itasca.Runtime.Compiler.Module.CompileAssembly

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Conservative source-only instruction demand for all module initializers. -/
def sourceInitializerInstructions (env : metadata.Env) (tail : metadata.Tail) : Nat :=
  2*initializerMappingCost ⟨env,tail⟩+5*(env.elements.length+tail.data.length)+1

/-- Independent numerical eligibility for a complete module compilation.
Environment metadata, source body maxima, aggregate function/initializer
charges, scratch requests, and intrinsic publication bounds are all explicit. -/
structure SourceCompilationDemand (A : Type) (env : metadata.Env) (tail : metadata.Tail)
    (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (bodyBytes localCount peak bound : Nat) : Prop where
  environment : EnvironmentDemand (initialScheduler A limits 0#usize) env bound
  functions : FunctionDemandEnvelope (initialScheduler A limits 0#usize).budget
    env.func_type_indices.val.length bodyBytes localCount peak bound
  maxima : SourcePreparationMaxima env profile bodyBytes localCount peak
  instructions : env.func_type_indices.val.length*(3*bodyBytes)+sourceInitializerInstructions env tail ≤ limits.max_instructions.val
  mappingCapacity : env.func_type_indices.val.length+initializerMappingCost ⟨env,tail⟩+1 ≤ Usize.max
  mappingReserve : env.func_type_indices.val.length+initializerMappingCost ⟨env,tail⟩+1 ≤ bound
  literalReserve : 2 ≤ bound
  segmentCapacity : 5*(env.elements.length+tail.data.length)+1 ≤ Usize.max
  segmentReserve : 5*(env.elements.length+tail.data.length)+1 ≤ bound
  elementCount : env.elements.length ≤ U32.max
  dataCount : tail.data.length ≤ U32.max
  elementLengths : ∀ segment ∈ env.elements.val, segment.init.length ≤ U32.max
  dataLengths : ∀ segment ∈ tail.data.val, segment.init.length ≤ U32.max
  queueReserve : 4 ≤ bound

/-- Aggregate source demand supplies the actual initializer phase after all
functions have consumed at most their conservative source-paid allowances. -/
theorem SourceCompilationDemand.initializers {A env tail profile limits bodyBytes localCount peak bound}
    (demand : SourceCompilationDemand A env tail profile limits bodyBytes localCount peak bound)
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (count : functions.length = env.func_type_indices.val.length) (budget : runtime.compiler.Budget A)
    (paid : CompilationBudgetEffect (initialScheduler A limits 0#usize).budget budget
      (fun counter => env.func_type_indices.val.length*functionDemandRate bodyBytes localCount counter)) :
    InitializerCompilationDemand (uninitializedModule env tail profile functions) budget bound := by
  have limitEq : budget.limits = limits := paid.limits
  have instructions := (paid.counts .instructions).2
  simp only [initialScheduler,ChargeCounter.used,functionDemandRate,show (0#usize).val = 0 from rfl,Nat.zero_add] at instructions
  have countVal : functions.val.length = env.func_type_indices.val.length := count
  constructor
  · have total := demand.instructions
    simp only [uninitializedModule,segmentCompilationDemand,limitEq]
    simp only [sourceInitializerInstructions,alloc.vec.Vec.length] at total
    omega
  · simpa [uninitializedModule,initializerSize,alloc.vec.Vec.new,alloc.vec.Vec.length,countVal] using demand.mappingCapacity
  · simpa [uninitializedModule,initializerSize,alloc.vec.Vec.new,alloc.vec.Vec.length,countVal] using demand.mappingReserve
  · exact demand.literalReserve
  · simpa [uninitializedModule,segmentCompilationDemand] using demand.segmentCapacity
  · simpa [uninitializedModule,segmentCompilationDemand] using demand.segmentReserve
  · exact demand.elementCount
  · exact demand.dataCount
  · exact demand.elementLengths
  · exact demand.dataLengths

/-- Fresh scheduler metadata demand is independent of the source coordinate
chosen by the scanner. -/
theorem SourceCompilationDemand.environment_at {A env tail profile limits bodyBytes localCount peak bound}
    (demand : SourceCompilationDemand A env tail profile limits bodyBytes localCount peak bound) (start : Usize) :
    EnvironmentDemand (initialScheduler A limits start) env bound := by
  have ready := demand.environment
  exact ⟨ready.functionLimit,ready.typeLimit,ready.signatureWidths,ready.functionWidths,
    ready.signatureCapacity,ready.signatureReserve,ready.slotCapacity,ready.slotReserve,
    ready.functionCapacity,ready.functionReserve⟩

end Itasca.Runtime.Compiler
