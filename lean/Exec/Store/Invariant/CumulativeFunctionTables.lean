import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Interp.Machines.Cumulative.CumulativeCompiledFunctions
namespace Exec.Store
open Aeneas Aeneas.Std


theorem cumulative_function_compiled_prefix {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {oldCode newCode : CodeInterpretation}
    (shape : Shape view before) (retained : StagedPrefix before after)
    (agrees : CodeAgreesOn before oldCode newCode) {function : runtime.store.Function}
    (compiled : Interp.CumulativeFunctionCompiled oldCode before function) :
    Interp.CumulativeFunctionCompiled newCode after function := by
  intro instanceIndex functionIndex defined
  obtain ⟨inst, code, signature, declared, body, epilogue,
    found, functionFound, signatureFound, source, table, types, certificate⟩ := compiled instanceIndex functionIndex defined
  refine ⟨inst, code, signature, declared, body, epilogue,
    Exec.Representation.lookup_prefix _ _ retained.instances found, functionFound,
    Exec.Representation.lookup_prefix _ _ retained.types signatureFound, ?_, function_table_prefix retained table, ?_, certificate⟩
  · rw [agrees instanceIndex.val inst found functionIndex.val]
    exact source
  · rw [decodeInstance_prefix before after retained inst (shape.instances inst (List.mem_of_getElem? found))]
    exact types

theorem cumulative_compiled_functions_retained {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {oldCode newCode : CodeInterpretation}
    (shape : Shape view before) (retained : StagedPrefix before after)
    (agrees : CodeAgreesOn before oldCode newCode)
    (compiled : Interp.CumulativeCompiledFunctions oldCode before) :
    ∀ function ∈ before.funcs.val, Interp.CumulativeFunctionCompiled newCode after function := by
  intro function present
  exact cumulative_function_compiled_prefix shape retained agrees (compiled function present)

theorem cumulative_compiled_functions_metadata {M : Type} {before after : runtime.store.Store M}
    (code : CodeInterpretation) (identity : after.id = before.id)
    (functions : after.funcs = before.funcs) (types : after.types = before.types)
    (instances : after.instances = before.instances)
    (compiled : Interp.CumulativeCompiledFunctions code before) : Interp.CumulativeCompiledFunctions code after := by
  simpa only [Interp.CumulativeCompiledFunctions, Interp.CumulativeFunctionCompiled, Interp.FunctionTable,
    decodeInstance, identity, functions, types, instances] using compiled
end Exec.Store
