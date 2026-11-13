import Itasca.Runtime.Compiler.Module.EnvironmentCompilationAvailable
import Itasca.Runtime.Compiler.Module.InitializerCompilationAvailable
import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Stream.DriverComplete

/-!
Sections, each formerly its own module: SourceCompilationDemand, SourceRegionsAvailable.
-/

/-! ## SourceCompilationDemand -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Conservative source-only instruction demand for all module initializers. -/
def sourceInitializerInstructions (env : metadata.Env) (tail : metadata.Tail) : Nat :=
  2*initializerMappingCost ⟨env,tail⟩+5*(env.elements.length+tail.data.length)+1

/-- Independent numerical eligibility for a complete module compilation.
Environment metadata, source body maxima, aggregate function/initializer
charges, scratch requests, and intrinsic publication bounds are all explicit. -/
structure SourceCompilationDemand (A : Type) (env : metadata.Env) (tail : metadata.Tail)
     (limits : runtime.compiler.CompileLimits)
    (bodyBytes localCount peak bound : Nat) : Prop where
  environment : EnvironmentDemand (initialScheduler A limits 0#usize) env bound
  functions : FunctionDemandEnvelope (initialScheduler A limits 0#usize).budget
    env.func_type_indices.val.length bodyBytes localCount peak bound
  maxima : SourcePreparationMaxima env bodyBytes localCount peak
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
theorem SourceCompilationDemand.initializers {A env tail limits bodyBytes localCount peak bound}
    (demand : SourceCompilationDemand A env tail limits bodyBytes localCount peak bound)
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (count : functions.length = env.func_type_indices.val.length) (budget : runtime.compiler.Budget A)
    (paid : CompilationBudgetEffect (initialScheduler A limits 0#usize).budget budget
      (fun counter => env.func_type_indices.val.length*functionDemandRate bodyBytes localCount counter)) :
    InitializerCompilationDemand (uninitializedModule env tail functions) budget bound := by
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
theorem SourceCompilationDemand.environment_at {A env tail limits bodyBytes localCount peak bound}
    (demand : SourceCompilationDemand A env tail limits bodyBytes localCount peak bound) (start : Usize) :
    EnvironmentDemand (initialScheduler A limits start) env bound := by
  have ready := demand.environment
  exact ⟨ready.functionLimit,ready.typeLimit,ready.signatureWidths,ready.functionWidths,
    ready.signatureCapacity,ready.signatureReserve,ready.slotCapacity,ready.slotReserve,
    ready.functionCapacity,ready.functionReserve⟩

end Itasca.Runtime.Compiler

end

/-! ## SourceRegionsAvailable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem slice_value (data region : Slice U8) (first last : Usize)
    (ordered : first.val ≤ last.val) (bounded : last.val ≤ data.length)
    (called : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) data ⟨first,last⟩ = .ok region) :
    region.val = data.val.slice first.val last.val := by
  have post := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec ⟨first,last⟩ data (by scalar_tac) bounded
  change core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first,last⟩ data = .ok region at called
  rw [called,WP.spec_ok] at post
  exact post.1

/-- The runtime's immutable source makes every region of the canonical split
available whenever its scanner selected those same byte coordinates. -/
theorem compiler_source_regions_available (data : Slice U8) (regions : Itasca.stream.SliceSource)
    (codeStart codeEnd : Usize)
    (split : StreamCompleteRegions.Split data regions)
    (selected : Itasca.stream.find_code_region data = .ok (codeStart,codeEnd)) :
    StreamSource.Available runtime.compiler.CompileSource.Insts.ItascaStreamSource
      {bytes := data,code_start := codeStart,code_end := codeEnd} regions.env.val regions.code.val regions.tail.val := by
  obtain ⟨first,last,scanned,environment,code,tail⟩ := split
  have same : first = codeStart ∧ last = codeEnd := by
    simpa only [Result.ok.injEq,Prod.mk.injEq] using scanned.symm.trans selected
  simp only [same.1,same.2] at environment code tail
  obtain ⟨ordered,bounded⟩ := Itasca.stream.find_code_region.bounds data codeStart codeEnd selected
  have envValue := slice_value data regions.env 0#usize codeStart (by simp) (by omega) environment
  have codeValue := slice_value data regions.code codeStart codeEnd ordered bounded code
  have tailValue := slice_value data regions.tail codeEnd (Slice.len data) (by simpa using bounded) (by simp) tail
  have envEq : regions.env.val = data.val.take codeStart.val := by simpa [List.slice] using envValue
  have tailEq : regions.tail.val = data.val.drop codeEnd.val := by
    simp only [List.slice,Slice.len_val] at tailValue
    rw [←List.length_drop] at tailValue
    simpa only [List.take_length] using tailValue
  have available := source_available ({bytes := data,code_start := codeStart,code_end := codeEnd} : runtime.compiler.CompileSource)
    ⟨ordered,bounded⟩
  simpa only [sourceEnvironment,sourceCode,sourceTail,←envEq,←codeValue,←tailEq] using available

end Itasca.Runtime.Compiler

end
