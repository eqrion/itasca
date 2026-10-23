import Exec.Interp.Relations.SourceValueCauses
import Exec.Interp.Machines.Core.CoreFunctionTyping
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The complete source module namespace. The data namespace is completed
from the parsed module tail, as in the canonical function-typing certificate. -/
def sourceCapacityContext (env : Itasca.module.Env) (dataCount : Nat) : context :=
  { Code.sourceFunctionContext env [] [] with
    DATAS := List.replicate dataCount datatype.OK, RETURN := none }

/-- A source frame requirement whose complete validation environment is tied
by semantic bindings to the actual source instance. The function is typed in
that same context. No compiled slot counter appears in this definition. -/
def SourceCanonicalFunctionCapacity (store : _root_.store) (address : funcaddr) (words : Nat) : Prop :=
  ∃ (function : funcinst) (profile : Itasca.ValidationProfile) (env : Itasca.module.Env)
      (typeIndex : U32) (dataCount : Nat),
    store.FUNCS[address]? = some function ∧
    SourceCapacityEnvironment store function env typeIndex ∧
    Abs.ModuleBindings store function.MODULE (sourceCapacityContext env dataCount) ∧
    (∃ index locals body, function.CODE = .FUNC index locals body ∧
      Func_ok (sourceCapacityContext env dataCount) (.FUNC index locals body) function.TYPE) ∧
    Code.SourceFrameCapacity profile env typeIndex function.CODE words

/-- Canonical module typing supplies every namespace required by full-profile
capacity traces, including mutable globals, tables, memories and segments. -/
theorem function_canonical_capacity_decoded {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (instanceIndex functionIndex : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction)
    (found : store.funcs.val[address.index.val]? = some function)
    (defined : function.code = .Wasm instanceIndex functionIndex)
    (instanceFound : store.instances.val[instanceIndex.val]? = some inst)
    (codeFound : inst.module.functions.val[functionIndex.val]? = some compiled) :
    ∃ words, SourceCanonicalFunctionCapacity (Store.decodeStore view code store) address.index.val words ∧
      compiled.slot_count.val ≤ words := by
  obtain ⟨actualInst,actualCode,typeIndex,actualFound,actualCodeFound,
      ⟨words,sourceCapacity,bound⟩,entries,table,signature,typeFound,signatureFound⟩ :=
    capacities function (List.mem_of_getElem? found) instanceIndex functionIndex defined
  have sameInst : actualInst = inst := Option.some.inj (actualFound.symm.trans instanceFound)
  subst actualInst
  have sameCode : actualCode = compiled := Option.some.inj (actualCodeFound.symm.trans codeFound)
  subst actualCode
  have functionTyped := typed function (List.mem_of_getElem? found)
  simp only [CoreFunctionTyped,defined] at functionTyped
  obtain ⟨typedInst,sourceIndex,locals,body,typedFound,sourceEq,bindings,sourceTyped⟩ := functionTyped
  have sameInst : typedInst = inst := Option.some.inj (typedFound.symm.trans instanceFound)
  subst typedInst
  have contextEq : Code.moduleSourceContext inst.module =
      sourceCapacityContext inst.module.module.env inst.module.module.tail.data.length := by rfl
  refine ⟨words,⟨Store.decodeFunction code store function,inst.module.profile,
    inst.module.module.env,typeIndex,inst.module.module.tail.data.length,?_,?_,?_,?_,?_⟩,bound⟩
  · simp only [Store.decodeStore,List.getElem?_map,found,Option.map_some]
  · constructor
    · simpa only [Store.decodeFunction,defined,instanceFound,Store.decodeInstance] using entries.capacity_decode
    · simpa only [Store.decodeFunction,defined,instanceFound] using table.source view code
    · refine ⟨signature,typeFound,?_⟩
      simp only [Store.decodeFunction,defined,instanceFound,List.getD_eq_getElem?_getD,
        List.getElem?_map,signatureFound,Option.map_some,Option.getD_some]
  · simpa only [Store.decodeFunction,defined,instanceFound,contextEq] using bindings
  · refine ⟨sourceIndex,locals,body,?_,?_⟩
    · simpa only [Store.decodeFunction,defined,instanceFound] using sourceEq
    · simpa only [contextEq] using sourceTyped
  · simpa only [Store.decodeFunction,defined,instanceFound] using sourceCapacity
end Exec.Interp
