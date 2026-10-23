import Exec.Code.Local.Callbacks.Common.CompilerMetadata
import Exec.Code.Local.Control.Table.StructuredFunctionBodyClose
import Exec.Code.Local.Control.Table.StructuredFunction
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Finishing the actual compiler assembles the retained function certificate.
The body relation and epilogue come from the completed source prefix; fixed
signature/local metadata is transported from the function-start callback. -/
theorem indexed_compiler_finish_certificate {A : Type} (ops : runtime.platform.Alloc A)
    (initial final : runtime.compiler.FunctionCompiler A)
    (validated : core.result.Result Unit Itasca.error.Error)
    (compiled : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (params declared results : List valtype)
    (body : List instr) (epilogue : U32)
    (stable : CompilerStable initial final)
    (signature : types[initial.function.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (locals : initial.function.locals.val.map Itasca.Translate.valueType = params ++ declared)
    (parameterSlots : initial.function.param_slots.val = slots params)
    (localSlots : initial.function.local_slots.val = slots (params ++ declared))
    (capacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (fetchBound : final.function.code.val.length ≤ U32.max)
    (bodyCode : StructuredCode emit types functions results (params ++ declared) final.function.code.val final.function.jump_tables.val
      [functionRootLabel results final.function epilogue] [] body 0 epilogue.val results)
    (returnCode : ∃ count, final.function.code.val[epilogue.val]? =
      some (.Return initial.function.local_slots count))
    (endPosition : final.function.code.val.length = epilogue.val + 1)
    (accepted : runtime.compiler.FunctionCompiler.finish ops final validated = .ok (.Ok compiled, budget)) :
    StructuredFunctionCode emit types functions params declared results body compiled epilogue := by
  obtain ⟨_, rfl, _, _, checked⟩ := compiler_finish_accepted ops final validated compiled budget accepted
  obtain ⟨_, _, _, typeEq, localsEq, paramsEq, slotsEq, _, _, _⟩ := stable.fields
  refine ⟨?_, ?_, ?_, ?_, ?_, fetchBound, checked, bodyCode, ?_, endPosition⟩
  · simpa only [typeEq] using signature
  · simpa only [localsEq] using locals
  · simpa only [paramsEq] using parameterSlots
  · simpa only [slotsEq] using localSlots
  · rw [slotsEq]
    exact capacity.trans stable.capacity
  · simpa only [slotsEq] using returnCode
end Exec.Code
