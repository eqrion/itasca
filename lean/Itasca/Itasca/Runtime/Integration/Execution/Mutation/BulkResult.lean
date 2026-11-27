import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Store.Initialization.SegmentOperations
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.SourceMachine.Float.Descriptors
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Compiler.Local.Control.FunctionAssembly
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Interp.State.GlobalOperations
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.Representation.Store
import Itasca.Runtime.SourceMachine.Stateful.TransitionInvariants

open Itasca.Representation

/-! ## Certificate -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std

theorem CumulativeStoreMutation.ownership_bounds {M : Type} {view : M → Slice U8}
    {code : Representation.CodeInterpretation} {before after : runtime.store.Store M}
    (mutation : CumulativeStoreMutation view code before after) :
    Store.ownershipBounds after = Store.ownershipBounds before := by
  unfold Store.ownershipBounds
  rw [mutation.metadata.functions,mutation.externs]

end Itasca.Integration

end

/-! ## GlobalShape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

private theorem encode_i32_small (value : val) (wellFormed : wf_val value)
    (typed : Representation.valueType value = .I32) : (Representation.encodeValue value)[0]! < 2^32 := by
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
      | I64 => simp [Representation.valueType,valtype_numtype,numtype_Inn] at typed
    | num__case_1 kind value hv hty =>
      subst ty
      cases kind <;> simp [Representation.valueType,valtype_numtype,numtype_Fnn] at typed
  | val_case_1 ty value _ _ => simp [Representation.valueType] at typed
  | val_case_2 ty => cases ty <;> simp [Representation.valueType] at typed
  | val_case_3 address => simp [Representation.valueType] at typed
  | val_case_4 address => simp [Representation.valueType] at typed

private theorem encoded_reference_shape {M : Type} (store : runtime.store.Store M)
    (ty : Itasca.wasm_types.ElemType) (word : U64) (value : val)
    (typed : Representation.valueType value = Itasca.Translation.valueType (match ty with | .FuncRef => .FuncRef | .ExternRef => .ExternRef))
    (represented : word.val = (Representation.encodeValue value)[0]!)
    (owned : SourceMachine.Ownership.ValueOwned ⟨store.funcs.length,store.externs.length⟩ value) :
    ReferenceShape store ty word := by
  cases value with
  | CONST type bits => cases type <;> cases ty <;> simp [Representation.valueType,Itasca.Translation.valueType,valtype_numtype,numtype_Inn,numtype_Fnn] at typed
  | VCONST type bits => cases ty <;> simp [Representation.valueType,Itasca.Translation.valueType] at typed
  | REF_NULL type =>
    exact Or.inl (by simpa [Representation.encodeValue] using represented)
  | REF_FUNC_ADDR address =>
    cases ty with
    | FuncRef =>
      apply Or.inr
      simpa [represented,Representation.encodeValue,SourceMachine.Ownership.ValueOwned] using owned
    | ExternRef => simp [Representation.valueType,Itasca.Translation.valueType] at typed
  | REF_HOST_ADDR address =>
    cases ty with
    | FuncRef => simp [Representation.valueType,Itasca.Translation.valueType] at typed
    | ExternRef =>
      apply Or.inr
      simpa [represented,Representation.encodeValue,SourceMachine.Ownership.ValueOwned] using owned

theorem global_encoded_shape {M : Type} (store : runtime.store.Store M)
    (old : runtime.store.GlobalInst) (lo hi : U64) (value : val)
    (prior : GlobalShape store old) (wellFormed : wf_val value)
    (typed : Itasca.Translation.valueType old.ty.valtype = Representation.valueType value)
    (represented : pairWords old.ty.valtype (lo,hi) = Representation.encodeValue value)
    (high : old.ty.valtype ≠ .V128 → hi = old.hi)
    (owned : SourceMachine.Ownership.ValueOwned ⟨store.funcs.length,store.externs.length⟩ value) :
    GlobalShape store {old with lo,hi} := by
  have low := congrArg (fun words : List Nat => words[0]!) represented
  cases kind : old.ty.valtype <;>
    simp only [GlobalShape,kind] at prior ⊢
  · refine ⟨?_,(high (by simp [kind])).trans prior.2⟩
    simp only [pairWords,kind,Itasca.Translation.valueType,reduceCtorEq,ite_false,List.getElem!_cons_zero] at low
    rw [low]
    exact encode_i32_small value wellFormed (by simpa [kind,Itasca.Translation.valueType] using typed.symm)
  · exact (high (by simp [kind])).trans prior
  · refine ⟨?_,(high (by simp [kind])).trans prior.2⟩
    simp only [pairWords,kind,Itasca.Translation.valueType,reduceCtorEq,ite_false,List.getElem!_cons_zero] at low
    rw [low]
    exact encode_value_f32_low value wellFormed (by simpa [kind,Itasca.Translation.valueType] using typed.symm)
  · exact (high (by simp [kind])).trans prior
  · refine ⟨encoded_reference_shape store .FuncRef lo value ?_ ?_ owned,(high (by simp [kind])).trans prior.2⟩
    · simpa [kind,Itasca.Translation.valueType] using typed.symm
    · simpa only [pairWords,kind,Itasca.Translation.valueType,reduceCtorEq,ite_false,List.getElem!_cons_zero] using low
  · refine ⟨encoded_reference_shape store .ExternRef lo value ?_ ?_ owned,(high (by simp [kind])).trans prior.2⟩
    · simpa [kind,Itasca.Translation.valueType] using typed.symm
    · simpa only [pairWords,kind,Itasca.Translation.valueType,reduceCtorEq,ite_false,List.getElem!_cons_zero] using low

theorem global_mutation_shape {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {value : val}
    (shape : Shape view before) (mutation : Interp.GlobalMutation before after value)
    (wellFormed : wf_val value)
    (owned : SourceMachine.Ownership.ValueOwned ⟨before.funcs.length,before.externs.length⟩ value) :
    Shape view after := by
  obtain ⟨index,old,lo,hi,found,mutable,typed,represented,high,rfl⟩ := mutation
  apply shape.global_replace
  exact global_encoded_shape before old lo hi value (shape.globals old (List.mem_of_getElem? found))
    wellFormed typed represented high owned
end Itasca.Store

end

/-! ## BulkResult -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Store Itasca.Interp

def statefulBulkResult {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : SourceMachine.AResult :=
  match out.1 with
  | .Ok _ => SourceMachine.advance {state with store := decodeStore view code out.2} {f with code := after,vals := front} rest
  | .Err _ => .trap

theorem bulk_integer_decoded (word : U64) :
    SourceMachine.integer .I32 (SourceMachine.integerVal .I32 (bulkWord word).val) = some (bulkWord word).val :=
  SourceMachine.integer_accepts .I32 _ (by change (bulkWord word).val < 2^32; simp only [bulkWord,U32.cast_U64_val_eq]; scalar_tac)
end Itasca.Integration

end
