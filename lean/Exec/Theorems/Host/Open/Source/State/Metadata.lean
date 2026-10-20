import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Theorems.Api.ExecutableInv
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- The source invocation signature is determined by the same raw function
and type metadata as the checked native call, for either function kind. -/
theorem source_function_signature {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (index : Usize) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature) :
    index.val<(Store.decodeStore view code store).FUNCS.length ∧
    (Store.decodeStore view code store).FUNCS[index.val]!.TYPE=Store.decodeFuncType signature := by
  have inside := (List.getElem?_eq_some_iff.mp functionAt).1
  have signatureBound := (List.getElem?_eq_some_iff.mp signatureAt).1
  have sourceBound : index.val<(Store.decodeStore view code store).FUNCS.length := by
    simpa only [Store.decodeStore,List.length_map] using inside
  have sourceAt : (Store.decodeStore view code store).FUNCS[index.val]?=some (Store.decodeFunction code store function) := by
    simp only [Store.decodeStore,List.getElem?_map,functionAt,Option.map_some]
  refine ⟨sourceBound,?_⟩
  rw [getElem!_pos (Store.decodeStore view code store).FUNCS index.val sourceBound,
    (List.getElem?_eq_some_iff.mp sourceAt).2,Store.decodeFunction_type code store function signatureBound,
    (List.getElem?_eq_some_iff.mp signatureAt).2]
end Exec.Theorems.OpenReentrantControl
