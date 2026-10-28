import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Interp.StructuredMachine.CompiledFunctions
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem supported_function_compiled_prefix {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {oldCode newCode : CodeInterpretation}
    (shape : Shape view before) (retained : StagedPrefix before after)
    (agrees : CodeAgreesOn before oldCode newCode) {function : runtime.store.FuncInst}
    (compiled : Interp.StructuredMachine.FunctionCompiled oldCode before function) :
    Interp.StructuredMachine.FunctionCompiled newCode after function := by
  intro instanceIndex functionIndex defined
  obtain ⟨inst, code, signature, declared, body, epilogue,
    found, functionFound, signatureFound, source, table, types, certificate⟩ := compiled instanceIndex functionIndex defined
  refine ⟨inst, code, signature, declared, body, epilogue,
    Itasca.Runtime.Representation.lookup_prefix _ _ retained.instances found, functionFound,
    Itasca.Runtime.Representation.lookup_prefix _ _ retained.types signatureFound, ?_, function_table_prefix retained table, ?_, certificate⟩
  · rw [agrees instanceIndex.val inst found functionIndex.val]
    exact source
  · rw [decodeInstance_prefix before after retained inst (shape.instances inst (List.mem_of_getElem? found))]
    exact types

end Itasca.Runtime.Store
