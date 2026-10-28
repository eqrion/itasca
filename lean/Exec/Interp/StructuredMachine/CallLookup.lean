import Exec.Interp.StructuredMachine.CompiledFunctions
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.CallSafety
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem CompiledFunctions.defined {M : Type} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (compiledFunctions : CompiledFunctions code store)
    (view : M → Slice U8) (typed : CoreFunctionsTyped view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (instanceIndex functionIndex : Usize)
    (lookup : store.funcs.val[address.index.val]? = some function)
    (defined : function.code = .Wasm instanceIndex functionIndex) :
    ∃ inst compiled signature declared body epilogue,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      store.types.val[function.signature.val]? = some signature ∧
      FunctionTable store inst (inst.module.module.env.func_types.val.map Store.decodeFuncType) ∧
      FunctionCode (Code.moduleFunctionContext inst.module
        (signature.params.val.map sourceType++declared) (signature.results.val.map sourceType))
        (signature.params.val.map sourceType) declared (signature.results.val.map sourceType) body compiled epilogue ∧
      Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst)
        (Code.moduleFunctionContext inst.module (signature.params.val.map sourceType++declared) (signature.results.val.map sourceType)) ∧
      (Store.decodeStore view code store).FUNCS[address.index.val]? =
        some ⟨Store.decodeFuncType signature,Store.decodeInstance store inst,
          .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body⟩ := by
  obtain ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,source,table,types,certificate⟩ :=
    compiledFunctions function (List.mem_of_getElem? lookup) instanceIndex functionIndex defined
  have sourceTyped := typed function (List.mem_of_getElem? lookup)
  simp only [CoreFunctionTyped,defined] at sourceTyped
  obtain ⟨actual,index,locals,instructions,found,bodyEq,bindings,functionTyped⟩ := sourceTyped
  have same : actual = inst := Option.some.inj (found.symm.trans hi)
  subst actual
  have contextBindings := bindings.scope (signature.params.val.map sourceType++declared) [] (some (.mk_list (signature.results.val.map sourceType)))
  exact ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,table,certificate,contextBindings,
    defined_function_lookup view code store address function signature instanceIndex functionIndex inst _ lookup hs defined hi source⟩
end Itasca.Runtime.Interp.StructuredMachine
