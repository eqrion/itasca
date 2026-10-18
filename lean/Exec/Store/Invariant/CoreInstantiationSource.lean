import Exec.Store.Invariant.CoreSourceFunctionInstances
import Exec.Store.Invariant.SourceCore
import Exec.Store.Invariant.InstantiationCode
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

theorem InstantiationCode.core_typed {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.Instance}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (raw : ModuleBinary.Module) (shape : Shape view before)
    (oldSyntax : StoreSyntax oldCode before)
    (oldTyped : Interp.CoreFunctionsTyped view oldCode before)
    (freshWf : wf_store (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready))
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (bindings : Abs.ModuleBindings
      (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready)
      (decodeInstance ready inst) (ModuleElaboration.contextOf raw)) :
    Interp.CoreFunctionsTyped view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  exact core_source_functions_publish_wf view before staged oldCode raw shape oldSyntax freshWf retained
    oldTyped inst found elaborated typed matched bindings signatures

theorem InstantiationCode.source_core {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.Instance}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (raw : ModuleBinary.Module) (shape : Shape view before)
    (oldSlice : Abs.CoreFunctions (decodeStore view oldCode before))
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (supported : Code.ModuleCore raw) :
    Abs.CoreFunctions (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready) := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  have functionsEq := congrArg ModuleBinary.Module.functions matched.1
  simp only [ModuleElaboration.fromEnv] at functionsEq
  have sourceCount : (Code.sourceFunctions raw).length = inst.module.module.env.func_type_indices.val.length := by
    rw [← functionsEq]
    simp only [Code.sourceFunctions, List.length_zipWith, elaborated.code_count, Nat.min_self]
  exact store_core_publish view before staged oldCode shape retained oldSlice inst (Code.sourceFunctions raw)
    sourceCount (Code.source_functions_core supported) found matched.2 signatures
end Exec.Store
