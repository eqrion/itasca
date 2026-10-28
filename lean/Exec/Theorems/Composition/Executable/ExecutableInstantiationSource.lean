import Exec.Store.Invariant.CoreInstantiationSource
import Exec.Theorems.Composition.SourceSupported
import Exec.Code.Local.Source.SourceExecutable
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca
theorem InstantiationCode.source_executable {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (raw : ModuleBinary.Module) (shape : Shape view before)
    (oldSlice : Abs.FunctionsSupported (decodeStore view oldCode before))
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    {profile bytes}
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes profile) :
    Abs.FunctionsSupported (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready) := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  have functionsEq := congrArg ModuleBinary.Module.functions matched.1
  simp only [ModuleElaboration.fromEnv] at functionsEq
  have sourceCount : (Code.sourceFunctions raw).length = inst.module.module.env.func_type_indices.val.length := by
    rw [← functionsEq]
    simp only [Code.sourceFunctions, List.length_zipWith, elaborated.code_count, Nat.min_self]
  exact store_supported_publish view before staged oldCode shape retained oldSlice inst (Code.sourceFunctions raw)
    sourceCount (Code.SourceExecutable.functions encoded) found matched.2 signatures
end Itasca.Runtime.Store
