import Itasca.Results.Definitions.Compiler.Compilation
import Itasca.Runtime.Compiler.Body.Definitions

/-! ## Function preparation and output storage -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Conservative per-function allowances expressed in source quantities.
The complete instruction allowance, including initializers, is stated separately
in `SourceCompilationDemand.instructions`. Branch entries, control records and
locals are bounded here by the number and maximum size of source functions.
No budget counter or mutable compiler state occurs in these conditions. -/
structure SourceFunctionDemand (limits : runtime.compiler.CompileLimits)
    (functions bodyBytes localCount peak bound : Nat) : Prop where
  size : bodyBytes ≤ Itasca.limits.MAX_FUNCTION_BYTES.val
  /-- Each branch-table entry consumes at least one source byte. -/
  branches : functions * bodyBytes ≤ limits.max_branch_table_entries.val
  /-- One implicit function control plus at most one control per source byte. -/
  controls : functions * (1 + bodyBytes) ≤ limits.max_controls.val
  localCharges : functions * localCount ≤ limits.max_locals.val
  temporary : 3 * bodyBytes + 3 ≤ bound
  locals : localCount ≤ bound
  operands : peak ≤ bound
  /-- Every value occupies at most two words, including vectors. -/
  slots : 2 * localCount + 2 * peak ≤ U32.max

end Itasca.Compiler

/-! ## Compiler / Module / PreparationDemand -/

section CompilerModulePreparationDemand

/-!
### Source preparation maxima

`SourcePreparationMaxima` bounds preparation resources from independently parsed module
declarations.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Uniform sufficient preparation bounds for the signatures of defined
functions. A body fits both the source byte allowance and the supported body cap;
declared locals use the supported local cap and parameters are additional locals. The operand allowance is 500 values per body byte, the
same conservative source-size estimate used by frame-capacity accounting.

This is deliberately a sufficient budget, not a measured peak. In particular,
no parser state, validator execution, chosen callback log or compiler artifact
is needed to interpret these inequalities. An environment without defined
functions has no body-preparation obligation. -/
def SourcePreparationMaxima (env : metadata.Env)
    (codeBytes bodyBytes localCount peak : Nat) : Prop :=
  ∀ typeIndex ∈ env.func_type_indices.val, ∀ signature,
    env.types.val[typeIndex.val]? = some signature →
    Nat.min codeBytes limits.MAX_FUNCTION_BYTES.val ≤ bodyBytes ∧
    signature.params.val.length + limits.MAX_LOCALS.val ≤ localCount ∧
    500 * Nat.min codeBytes limits.MAX_FUNCTION_BYTES.val ≤ peak

end Itasca.Compiler

end CompilerModulePreparationDemand

/-! ## Compiler / Module / Demand -/

section CompilerModuleDemand

/-!
### Source compilation demand

Initializer instruction demand and `SourceCompilationDemand` derive compiler resources
from the independent source regions.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std Itasca

/-- Conservative source-only instruction demand for all module initializers. -/
def sourceInitializerInstructions (env : metadata.Env) (tail : metadata.Tail) : Nat :=
  2*initializerMappingCost ⟨env,tail⟩+5*(env.elements.length+tail.data.length)+1

/-- Independent numerical eligibility for a complete module compilation.
Environment metadata, source body maxima, aggregate function/initializer
charges, scratch requests, and intrinsic publication bounds are all explicit. -/
structure SourceCompilationDemand (env : metadata.Env) (tail : metadata.Tail)
     (limits : runtime.compiler.CompileLimits)
    (codeBytes bodyBytes localCount peak bound : Nat) : Prop where
  environment : SourceEnvironmentDemand limits env bound
  functions : SourceFunctionDemand limits
    env.func_type_indices.val.length bodyBytes localCount peak bound
  maxima : SourcePreparationMaxima env codeBytes bodyBytes localCount peak
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

end Itasca.Compiler

end CompilerModuleDemand


namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Internal eligibility used by the existing compilation proof. SourceBudget
derives these metadata and preparation witnesses from the public computed budget. -/
structure InternalCompileEligible (bytes : Slice U8)
    (raw : Binary.Module) (limits : runtime.compiler.CompileLimits) (bound : Nat) : Prop where
  moduleBytes : bytes.length ≤ limits.max_module_bytes.val
  demand : ∀ env tail, Module.Elaboration.Matches env tail raw →
    ∃ bodyBytes localCount peak, SourceCompilationDemand env tail limits bytes.length bodyBytes localCount peak bound


end Itasca.Compiler

/-!
# Internal whole-module compilation certificate

This boundary joins function emission, initializer mappings and frame capacities.
Compiler construction uses the fields independently; integration consumes the
assembled certificate when proving instantiation. None is a public premise.

The module stays above Body and below the instantiation proof so compiler code
never imports interpreter execution. Public compilation exports only the source
and metadata association from Interface/Compiler/Module.
-/

/-! ## Integration / Compilation -/

section IntegrationCompilation

/-!
### Compilation certificates

One independent source module accounts for accepted bytes, returned metadata, compiled
function/initializer code and decoded frame capacities.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std Itasca

/-- Module-level compiler correspondence retains exact source ordering,
function-local instruction/table certificates, initializers, and decoded frame
capacities. Its code premises are syntactic relations, not assumed execution. -/
structure ModuleCodeRel (raw : Binary.Module)
    (executable : runtime.compiler.ExecutableModule) : Prop where
  /-- Parsed environment and tail describe this same raw source module. -/
  metadata : Module.Elaboration.Matches executable.module.env executable.module.tail raw
  /-- Public import/export accessors return the source module's external types. -/
  accessors : Module.Elaboration.AccessorTypes executable.module.env raw
  /-- Every defined function has its source-ordered syntactic code certificate. -/
  functions : Compiler.ExecutableModuleFunctions executable (Compiler.sourceFunctions raw)
  /-- Global, element and data initializers retain their source mappings. -/
  initializers : Compiler.InitializerMappings executable
  /-- Compiled frames carry the capacities required by their source functions. -/
  capacities : Compiler.ModuleCapacities executable (Compiler.sourceFunctions raw)

/-- The accepted binary and its compiled code share one canonical source module
under the Wasm 2.0 typing and module restrictions. -/
def CompilationCertificate (bytes : Slice U8)
    (executable : runtime.compiler.ExecutableModule) : Prop :=
  ∃ raw, Binary.ModuleEncodingWith CodeEntry.CodeEncoding raw bytes.val ∧
    Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw) ∧
    Module_ok (Module.Elaboration.moduleOf raw) ∧ Module.Elaboration.Restrictions raw ∧
    ModuleCodeRel raw executable

end Itasca.Integration

end IntegrationCompilation

