import Itasca.Runtime.Store.Invariant.CoreInstantiationSource
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Compiler.Local.Source.SourceExecutable
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca
theorem InstantiationCode.source_executable {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (raw : ModuleBinary.Module) (shape : Shape view before)
    (oldSlice : SourceMachine.FunctionsSupported (decodeStore view oldCode before))
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    {profile bytes}
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes profile) :
    SourceMachine.FunctionsSupported (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready) := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  have functionsEq := congrArg ModuleBinary.Module.functions matched.1
  simp only [ModuleElaboration.fromEnv] at functionsEq
  have sourceCount : (Compiler.sourceFunctions raw).length = inst.module.module.env.func_type_indices.val.length := by
    rw [← functionsEq]
    simp only [Compiler.sourceFunctions, List.length_zipWith, elaborated.code_count, Nat.min_self]
  exact store_supported_publish view before staged oldCode shape retained oldSlice inst (Compiler.sourceFunctions raw)
    sourceCount (Compiler.SourceExecutable.functions encoded) found matched.2 signatures
end Itasca.Runtime.Store
