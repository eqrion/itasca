import Exec.Code.Body.Reader.Common.ReaderCompilerRoot
import Exec.Code.Local.Relations.Common.FunctionAssembly
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The final executable check turns a completed actual body compilation into
its retained source certificate, with the original function-start metadata. -/
theorem CompiledBody.finish {A : Type} (ops : runtime.platform.Alloc A)
    {initial final : runtime.compiler.FunctionCompiler A}
    {types functions params declared results source}
    (body : CompiledBody initial final types functions results (params ++ declared) source)
    (signature : types[initial.function.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (locals : initial.function.locals.val.map Translate.valueType = params ++ declared)
    (parameterSlots : initial.function.param_slots.val = slots params)
    (localSlots : initial.function.local_slots.val = slots (params ++ declared))
    (capacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (validated : core.result.Result Unit error.Error)
    (compiled : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (accepted : runtime.compiler.FunctionCompiler.finish ops final validated = .ok (.Ok compiled, budget)) :
    ∃ epilogue, FunctionCode types functions params declared results source compiled epilogue := by
  obtain ⟨epilogue, stable, empty, code, ⟨src, count, srcWords, fetched⟩, ending, bound⟩ := body
  have sourceEq : src = initial.function.local_slots := by
    apply UScalar.eq_of_val_eq
    exact srcWords.trans localSlots.symm
  refine ⟨epilogue, compiler_finish_certificate ops initial final validated compiled budget types functions
    params declared results source epilogue stable signature locals parameterSlots localSlots capacity
    bound code ?_ ending accepted⟩
  exact ⟨count, by simpa only [sourceEq] using fetched⟩
end Exec.Code
