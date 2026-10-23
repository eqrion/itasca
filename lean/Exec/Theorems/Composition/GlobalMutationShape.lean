import Exec.Interp.State.GlobalMutation
import Exec.Abs.Ownership.Bounds
import Exec.Representation.StoreInvariant
namespace Exec.Store
open Aeneas Aeneas.Std
open Exec.Interp

private theorem encode_i32_small (value : val) (wellFormed : wf_val value)
    (typed : Code.valueType value = .I32) : (Code.encodeValue value)[0]! < 2^32 := by
  cases wellFormed with
  | val_case_0 ty value hv =>
    cases hv with
    | num__case_0 kind bits _ hb hty =>
      subst ty
      cases kind with
      | I32 => cases hb with
        | uN_case_0 bits bounds =>
          change Nat at bits
          have bound : bits ≤ 4294967295 := bounds.2
          change bits < 2^32
          omega
      | I64 => simp [Code.valueType,valtype_numtype,numtype_Inn] at typed
    | num__case_1 kind value hv hty =>
      subst ty
      cases kind <;> simp [Code.valueType,valtype_numtype,numtype_Fnn] at typed
  | val_case_1 ty value _ _ => simp [Code.valueType] at typed
  | val_case_2 ty => cases ty <;> simp [Code.valueType] at typed
  | val_case_3 address => simp [Code.valueType] at typed
  | val_case_4 address => simp [Code.valueType] at typed

private theorem encoded_reference_shape {M : Type} (store : runtime.store.Store M)
    (ty : Itasca.types.ElemType) (word : U64) (value : val)
    (typed : Code.valueType value = sourceType (match ty with | .FuncRef => .FuncRef | .ExternRef => .ExternRef))
    (represented : word.val = (Code.encodeValue value)[0]!)
    (owned : Abs.Ownership.ValueOwned ⟨store.funcs.length,store.externs.length⟩ value) :
    ReferenceShape store ty word := by
  cases value with
  | CONST type bits => cases type <;> cases ty <;> simp [Code.valueType,sourceType,valtype_numtype,numtype_Inn,numtype_Fnn] at typed
  | VCONST type bits => cases ty <;> simp [Code.valueType,sourceType] at typed
  | REF_NULL type =>
    exact Or.inl (by simpa [Code.encodeValue] using represented)
  | REF_FUNC_ADDR address =>
    cases ty with
    | FuncRef =>
      apply Or.inr
      simpa [represented,Code.encodeValue,Abs.Ownership.ValueOwned] using owned
    | ExternRef => simp [Code.valueType,sourceType] at typed
  | REF_HOST_ADDR address =>
    cases ty with
    | FuncRef => simp [Code.valueType,sourceType] at typed
    | ExternRef =>
      apply Or.inr
      simpa [represented,Code.encodeValue,Abs.Ownership.ValueOwned] using owned

theorem global_encoded_shape {M : Type} (store : runtime.store.Store M)
    (old : runtime.store.GlobalInst) (lo hi : U64) (value : val)
    (prior : GlobalShape store old) (wellFormed : wf_val value)
    (typed : sourceType old.ty.valtype = Code.valueType value)
    (represented : pairWords old.ty.valtype (lo,hi) = Code.encodeValue value)
    (high : old.ty.valtype ≠ .V128 → hi = old.hi)
    (owned : Abs.Ownership.ValueOwned ⟨store.funcs.length,store.externs.length⟩ value) :
    GlobalShape store {old with lo,hi} := by
  have low := congrArg (fun words : List Nat => words[0]!) represented
  cases kind : old.ty.valtype <;>
    simp only [GlobalShape,kind] at prior ⊢
  · refine ⟨?_,(high (by simp [kind])).trans prior.2⟩
    simp only [pairWords,kind,sourceType,reduceCtorEq,ite_false,List.getElem!_cons_zero] at low
    rw [low]
    exact encode_i32_small value wellFormed (by simpa [kind,sourceType] using typed.symm)
  · exact (high (by simp [kind])).trans prior
  · refine ⟨?_,(high (by simp [kind])).trans prior.2⟩
    simp only [pairWords,kind,sourceType,reduceCtorEq,ite_false,List.getElem!_cons_zero] at low
    rw [low]
    exact encodeValue_f32_low value wellFormed (by simpa [kind,sourceType] using typed.symm)
  · exact (high (by simp [kind])).trans prior
  · refine ⟨encoded_reference_shape store .FuncRef lo value ?_ ?_ owned,(high (by simp [kind])).trans prior.2⟩
    · simpa [kind,sourceType] using typed.symm
    · simpa only [pairWords,kind,sourceType,reduceCtorEq,ite_false,List.getElem!_cons_zero] using low
  · refine ⟨encoded_reference_shape store .ExternRef lo value ?_ ?_ owned,(high (by simp [kind])).trans prior.2⟩
    · simpa [kind,sourceType] using typed.symm
    · simpa only [pairWords,kind,sourceType,reduceCtorEq,ite_false,List.getElem!_cons_zero] using low

theorem global_mutation_shape {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {value : val}
    (shape : Shape view before) (mutation : Interp.GlobalMutation before after value)
    (wellFormed : wf_val value)
    (owned : Abs.Ownership.ValueOwned ⟨before.funcs.length,before.externs.length⟩ value) :
    Shape view after := by
  obtain ⟨index,old,lo,hi,found,mutable,typed,represented,high,rfl⟩ := mutation
  apply shape.global_replace
  exact global_encoded_shape before old lo hi value (shape.globals old (List.mem_of_getElem? found))
    wellFormed typed represented high owned
end Exec.Store
