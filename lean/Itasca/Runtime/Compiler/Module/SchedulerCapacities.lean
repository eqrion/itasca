import Itasca.Runtime.Compiler.Module.InitializerTotal
import Itasca.Runtime.Compiler.Module.CompileDriverFrame
import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedRawInitial
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.Return
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Support.Result
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericLowering
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlKind
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeWasm2
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Body.Capacity.ExecutableFunctionCapacity

/-!
Sections, each formerly its own module: CompileSchedulerAssembly, CompileSourceSetup, CompileSlice, SchedulerCapacities.
-/

/-! ## CompileSchedulerAssembly -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem source_functions_length {raw : ModuleBinary.Module}
    (count : raw.functions.length = raw.codes.length) :
    (sourceFunctions raw).length = raw.functions.length := by
  simp [sourceFunctions, List.length_zipWith, count]

end Itasca.Runtime.Compiler

end

/-! ## CompileSourceSetup -/

section

/-! Shared scheduler configuration and code-coordinate transport for source
certificates. Function, slice and capacity proofs retain their distinct folds. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Configuration facts used by each source-ordered compiler body fold. -/
theorem CompileSourceCertificate.scheduler_setup {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    SignatureSequence c.run.remaining.configured.signatures.val w.env.types.val ∧
      c.run.remaining.configured.func_param_slots.val.map (fun word => word.val) =
        w.env.func_types.val.map (fun ft => signatureSlots ft.params.val) ∧
      c.run.remaining.configured.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  refine ⟨prepared.1,prepared.2.1,?_⟩
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  rw [prepared.2.2.2]
  change w.codeStart.val ≤ _
  exact bounds.1.trans (bounds.2.trans c.moduleBound)

/-- Transport the actual reader's code length to the coherent source slice. -/
theorem CompileSourceCertificate.code_length {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) : c.run.remaining.codeLength = Slice.len c.code := by
  apply UScalar.eq_of_val_eq
  exact c.coherent.code_len_eq _ c.run.remaining.length_call
end Itasca.Runtime.Compiler

end

/-! ## CompileSlice -/

section

/-! Source-ordered slice certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual concrete source supplies every exact read used by the retained
canonical code-section certificate. -/
theorem CompileSourceCertificate.available {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) :
    StreamSource.Available runtime.compiler.CompileSource.Insts.ItascaStreamSource
      {bytes, code_start := w.codeStart, code_end := w.codeEnd} c.environment.val c.code.val c.tail.val := by
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  let source : runtime.compiler.CompileSource := {bytes, code_start := w.codeStart, code_end := w.codeEnd}
  have actual := source_available source bounds
  obtain ⟨len, readLen, length⟩ := actual.code_len_read
  have codeLength := c.coherent.code_len_eq len readLen
  constructor
  · obtain ⟨buffer, read, _⟩ := actual.environment_read
    exact ⟨buffer, read, c.coherent.environment_eq buffer read⟩
  · exact ⟨len, readLen, codeLength⟩
  · intro first last order bound
    obtain ⟨buffer, read, _⟩ := actual.code_read first last order (by omega)
    exact ⟨buffer, read, c.coherent.code_eq first last buffer order bound read⟩
  · obtain ⟨buffer, read, _⟩ := actual.tail_read
    exact ⟨buffer, read, c.coherent.tail_eq buffer read⟩

end Itasca.Runtime.Compiler

end

/-! ## SchedulerCapacities -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Capacity certificates retained in the scheduler's sparse vector. -/
structure PendingModuleCapacities (env : metadata.Env)
    (pending : List (Option runtime.bytecode.CompiledFunction)) (sources : List funccode) : Prop where
  count : sources.length = env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32), env.func_type_indices.val[index]? = some typeIndex →
    ∃ compiled source, pending[index]? = some (some compiled) ∧ sources[index]? = some source ∧
      FunctionCapacity env typeIndex source compiled

theorem PendingModuleCapacities.collected {env pending sources}
    (certificate : PendingModuleCapacities env pending sources)
    (module : runtime.compiler.ExecutableModule) (sameEnv : module.module.env = env)

    (collected : pending = module.functions.val.map some) : ModuleCapacities module sources := by
  refine ⟨by simpa only [sameEnv] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, source, codeFound, sourceFound, code⟩ := certificate.entry index typeIndex
    (by simpa only [sameEnv] using found)
  refine ⟨compiled, source, ?_, sourceFound, by simpa only [sameEnv] using code⟩
  rw [collected, List.getElem?_map] at codeFound
  cases actual : module.functions.val[index]? <;> simp_all

/-- Every occupied scheduler slot carries the corresponding declared function
certificate. Empty slots are permitted until actual collection succeeds. -/
structure PartialModuleCapacities (env : metadata.Env) (sources : List funccode)
    (pending : List (Option runtime.bytecode.CompiledFunction)) : Prop where
  count : pending.length = env.func_type_indices.val.length
  sourceCount : sources.length = env.func_type_indices.val.length
  entry : ∀ (index : Nat) (compiled : runtime.bytecode.CompiledFunction),
    pending[index]? = some (some compiled) →
    ∃ typeIndex source, env.func_type_indices.val[index]? = some typeIndex ∧
      sources[index]? = some source ∧ FunctionCapacity env typeIndex source compiled

theorem PartialModuleCapacities.empty (env : metadata.Env) (sources : List funccode)
    (count : sources.length = env.func_type_indices.val.length) :
    PartialModuleCapacities env sources (List.replicate env.func_type_indices.val.length none) := by
  refine ⟨by simp, count, ?_⟩
  intro index compiled found
  have member := List.mem_of_getElem? found
  simp at member

theorem PartialModuleCapacities.set {env sources pending}
    (certificate : PartialModuleCapacities env sources pending)
    (index : Nat) (typeIndex : U32) (compiled : runtime.bytecode.CompiledFunction) (source : funccode)
    (lookup : env.func_type_indices.val[index]? = some typeIndex)
    (sourceLookup : sources[index]? = some source)
    (code : FunctionCapacity env typeIndex source compiled) :
    PartialModuleCapacities env sources (pending.set index (some compiled)) := by
  refine ⟨by simpa using certificate.count, certificate.sourceCount, ?_⟩
  intro other value found
  by_cases equal : other = index
  · subst other
    have bound : index < pending.length := by
      rw [certificate.count]
      exact (List.getElem?_eq_some_iff.mp lookup).1
    have same : compiled = value := by simpa [List.getElem?_set, bound] using found
    subst value
    exact ⟨typeIndex, source, lookup, sourceLookup, code⟩
  · apply certificate.entry other value
    simpa [List.getElem?_set, equal] using found

/-- The accepted entry's actual source-indexed write preserves all earlier
certificates and installs precisely its newly checked function. -/
theorem CompileEntryWitness.capacities {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch)
     {env : metadata.Env} {sources : List funccode}
    (certificate : PartialModuleCapacities env sources before.functions.val)
    (typeIndex : U32) (source : funccode)
    (lookup : env.func_type_indices.val[w.entry.index.val]? = some typeIndex)
    (sourceLookup : sources[w.entry.index.val]? = some source)
    (code : FunctionCapacity env typeIndex source w.final.function) :
    PartialModuleCapacities env sources after.functions.val := by
  rw [w.published]
  simpa only [alloc.vec.Vec.set_val_eq] using certificate.set w.entry.index.val typeIndex w.final.function source lookup sourceLookup code

/-- Successful dense collection fills every slot, allowing the retained
per-index source witnesses to be assembled into the complete module list. -/
theorem PartialModuleCapacities.complete {env sources pending}
    (certificate : PartialModuleCapacities env sources pending)
    (functions : List runtime.bytecode.CompiledFunction)
    (collected : pending = functions.map some) :
    PendingModuleCapacities env pending sources := by
  have length : functions.length = env.func_type_indices.val.length := by
    simpa only [collected, List.length_map] using certificate.count
  refine ⟨certificate.sourceCount, ?_⟩
  intro index typeIndex lookup
  have bound : index < functions.length := by
    rw [length]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  have found : pending[index]? = some (some functions[index]) := by simp [collected, bound]
  obtain ⟨actualType, source, actualLookup, sourceLookup, code⟩ := certificate.entry index functions[index] found
  have same : actualType = typeIndex := by simpa [lookup] using actualLookup.symm
  subst actualType
  exact ⟨functions[index], source, found, sourceLookup, code⟩
end Itasca.Runtime.Compiler

end
