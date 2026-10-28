import Exec.Store.Invariant.CoreSourceFunctionInstances
import Exec.Code.Local.Source.SourceSlice
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.FunctionSignatures
import Exec.Store.Initialization.SegmentCodeMetadata
import Exec.Store.Invariant.InstantiationCode
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem InstantiationCode.core_typed {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
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

end Itasca.Runtime.Store
