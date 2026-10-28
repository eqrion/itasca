import Itasca.Runtime.Store.Api.ApiMetadata
import Itasca.Runtime.Store.Invariant.TypeEquality
import Itasca.Runtime.Spec.ExtensionTyping

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- An issued raw host entry decodes to the host identity and its exact signature. -/
theorem decode_host_function {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (identity : U64) (signature : Itasca.types.FuncType)
    (found : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureFound : store.types.val[function.signature.val]? = some signature) :
    SpecExt.HostFunction (decodeStore view code store) address.index.val identity.val
      (signature.params.val.map Interp.sourceType) (signature.results.val.map Interp.sourceType) := by
  refine ⟨default,?_⟩
  simp only [decodeStore,List.getElem?_map,found,Option.map_some,decodeFunction,host,
    List.getD_eq_getElem?_getD,List.getElem?_map,signatureFound,Option.map_some,Option.getD_some,
    decodeFuncType]

/-- Generated store extension fixes the called function's source type. The
post-callback lookup therefore recovers the original raw signature, even if
its internal type-table index changed. -/
theorem host_signature_extension {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (found : before.funcs.val[address.index.val]? = some function)
    (signatureFound : before.types.val[function.signature.val]? = some signature)
    (shape : Shape view after)
    (extension : Extend_store (decodeStore view code before) (decodeStore view code after)) :
    ∃ nextFunction, after.funcs.val[address.index.val]? = some nextFunction ∧
      after.types.val[nextFunction.signature.val]? = some signature := by
  obtain ⟨_,_,_,functions,_,_⟩ := Spec.extend_store_objects extension
  have oldBound := (List.getElem?_eq_some_iff.mp found).1
  have sourceBound : address.index.val < (decodeStore view code before).FUNCS.length := by
    simpa only [decodeStore,List.length_map] using oldBound
  have newBound : address.index.val < after.funcs.val.length := by
    have bound := sourceBound.trans_le functions.1
    simpa only [decodeStore,List.length_map] using bound
  let nextFunction := after.funcs.val[address.index.val]
  have nextFound : after.funcs.val[address.index.val]? = some nextFunction := by
    simp only [List.getElem?_eq_getElem newBound,nextFunction]
  have nextShape := shape.functions nextFunction (List.getElem_mem newBound)
  have sigBound : nextFunction.signature.val < after.types.val.length := nextShape.1
  let nextSignature := after.types.val[nextFunction.signature.val]
  have nextSig : after.types.val[nextFunction.signature.val]? = some nextSignature := by
    simp only [List.getElem?_eq_getElem sigBound,nextSignature]
  have equal := congrArg funcinst.TYPE (Spec.extend_func_eq (functions.2 address.index.val sourceBound))
  have oldSigBound := (List.getElem?_eq_some_iff.mp signatureFound).1
  have oldSigEqual := (List.getElem?_eq_some_iff.mp signatureFound).2
  have nextSigEqual := (List.getElem?_eq_some_iff.mp nextSig).2
  have decoded : decodeFuncType nextSignature = decodeFuncType signature := by
    simpa only [decodeStore,List.getElem!_eq_getElem?_getD,List.getElem?_map,
      found,nextFound,Option.map_some,Option.getD_some,
      decodeFunction_type code before function oldSigBound,
      decodeFunction_type code after nextFunction sigBound,oldSigEqual,nextSigEqual] using equal
  have same := decodeFuncType_injective decoded
  exact ⟨nextFunction,nextFound,by rw [←same]; exact nextSig⟩
end Itasca.Runtime.Store
