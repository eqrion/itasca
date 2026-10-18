import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Lowering.Float.FloatCoreFunctionContext
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Concrete function lookup retains the canonical source context for mutable
instructions. This is source syntax and layout evidence, independent of any
claim about execution or mutable store contents. -/
def FloatCoreFunctionCompiled {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.Function) : Prop :=
  ∀ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex →
    ∃ inst compiled signature declared body epilogue,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      store.types.val[function.signature.val]? = some signature ∧
      code instanceIndex.val inst.module functionIndex.val =
        .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body ∧
      FunctionTable store inst (inst.module.module.env.func_types.val.map Store.decodeFuncType) ∧
      (Store.decodeInstance store inst).TYPES = inst.module.module.env.types.val.map Store.decodeFuncType ∧
      Code.FloatCoreFunctionCode (Code.moduleFunctionContext inst.module
        (signature.params.val.map sourceType ++ declared) (signature.results.val.map sourceType))
        (signature.params.val.map sourceType) declared (signature.results.val.map sourceType)
        body compiled epilogue

def FloatCoreCompiledFunctions {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, FloatCoreFunctionCompiled code store function

theorem float_core_declared_types_not_bottom {C params declared results body compiled epilogue}
    (certificate : Code.FloatCoreFunctionCode C params declared results body compiled epilogue) :
    Forall (fun ty => ty ≠ valtype.BOT) declared := by
  intro ty member
  have present : ty ∈ params ++ declared := List.mem_append_right _ member
  rw [← certificate.2.locals] at present
  obtain ⟨rawType, _, rfl⟩ := List.mem_map.mp present
  cases rawType <;> decide
end Exec.Interp
