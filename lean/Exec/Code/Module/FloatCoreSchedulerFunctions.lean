import Exec.Code.Module.CompileSubmit
import Exec.Code.Module.FloatCoreCollectedFunctions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Every occupied scheduler slot carries the corresponding declared function
certificate. Empty slots are permitted until actual collection succeeds. -/
structure PartialFloatCoreModuleFunctions (env : module.Env) (sources : List funccode)
    (pending : List (Option runtime.bytecode.CompiledFunction)) : Prop where
  count : pending.length = env.func_type_indices.val.length
  sourceCount : sources.length = env.func_type_indices.val.length
  entry : ∀ (index : Nat) (compiled : runtime.bytecode.CompiledFunction),
    pending[index]? = some (some compiled) →
    ∃ typeIndex source, env.func_type_indices.val[index]? = some typeIndex ∧
      sources[index]? = some source ∧ DefinedFloatCoreFunctionCode env typeIndex source compiled

theorem PartialFloatCoreModuleFunctions.empty (env : module.Env) (sources : List funccode)
    (count : sources.length = env.func_type_indices.val.length) :
    PartialFloatCoreModuleFunctions env sources (List.replicate env.func_type_indices.val.length none) := by
  refine ⟨by simp, count, ?_⟩
  intro index compiled found
  have member := List.mem_of_getElem? found
  simp at member

theorem PartialFloatCoreModuleFunctions.set {env sources pending}
    (certificate : PartialFloatCoreModuleFunctions env sources pending)
    (index : Nat) (typeIndex : U32) (compiled : runtime.bytecode.CompiledFunction) (source : funccode)
    (lookup : env.func_type_indices.val[index]? = some typeIndex)
    (sourceLookup : sources[index]? = some source)
    (code : DefinedFloatCoreFunctionCode env typeIndex source compiled) :
    PartialFloatCoreModuleFunctions env sources (pending.set index (some compiled)) := by
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
theorem CompileEntryWitness.float_core_functions {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch)
    {env : module.Env} {sources : List funccode}
    (certificate : PartialFloatCoreModuleFunctions env sources before.functions.val)
    (typeIndex : U32) (source : funccode)
    (lookup : env.func_type_indices.val[w.entry.index.val]? = some typeIndex)
    (sourceLookup : sources[w.entry.index.val]? = some source)
    (code : DefinedFloatCoreFunctionCode env typeIndex source w.final.function) :
    PartialFloatCoreModuleFunctions env sources after.functions.val := by
  rw [w.published]
  simpa only [alloc.vec.Vec.set_val_eq] using certificate.set w.entry.index.val typeIndex w.final.function source lookup sourceLookup code

/-- Successful dense collection fills every slot, allowing the retained
per-index source witnesses to be assembled into the complete module list. -/
theorem PartialFloatCoreModuleFunctions.complete {env sources pending}
    (certificate : PartialFloatCoreModuleFunctions env sources pending)
    (functions : List runtime.bytecode.CompiledFunction)
    (collected : pending = functions.map some) :
    PendingFloatCoreModuleFunctions env pending sources := by
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
end Exec.Code
