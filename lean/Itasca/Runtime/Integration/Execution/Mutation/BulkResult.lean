import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.ErrorPost
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.SourceMachine.Stateful.Bound

/-!
Sections, each formerly its own module: Certificate, GlobalShape, BulkResult.
-/

/-! ## Certificate -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

/-- An internal dispatch witness, established from exact runtime mutation
footprints. Segment contents may change; their checked bounds remain explicit. -/
structure CumulativeStoreMutation {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M) : Prop where
  metadata : Interp.FrameStoreMetadata before after
  externs : after.externs = before.externs
  shape : Store.Shape view after
  segmentBounds : Store.SegmentBounds after
  extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after)
  segmentCounts : Store.SegmentCounts before after
  limits : after.limits = before.limits

theorem CumulativeStoreMutation.ownership_bounds {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (mutation : CumulativeStoreMutation view code before after) :
    Store.ownershipBounds after = Store.ownershipBounds before := by
  unfold Store.ownershipBounds
  rw [mutation.metadata.functions,mutation.externs]

end Itasca.Runtime.Integration

end

/-! ## GlobalShape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

private theorem encode_i32_small (value : val) (wellFormed : wf_val value)
    (typed : Compiler.valueType value = .I32) : (Compiler.encodeValue value)[0]! < 2^32 := by
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
      | I64 => simp [Compiler.valueType,valtype_numtype,numtype_Inn] at typed
    | num__case_1 kind value hv hty =>
      subst ty
      cases kind <;> simp [Compiler.valueType,valtype_numtype,numtype_Fnn] at typed
  | val_case_1 ty value _ _ => simp [Compiler.valueType] at typed
  | val_case_2 ty => cases ty <;> simp [Compiler.valueType] at typed
  | val_case_3 address => simp [Compiler.valueType] at typed
  | val_case_4 address => simp [Compiler.valueType] at typed

private theorem encoded_reference_shape {M : Type} (store : runtime.store.Store M)
    (ty : Itasca.wasm_types.ElemType) (word : U64) (value : val)
    (typed : Compiler.valueType value = sourceType (match ty with | .FuncRef => .FuncRef | .ExternRef => .ExternRef))
    (represented : word.val = (Compiler.encodeValue value)[0]!)
    (owned : SourceMachine.Ownership.ValueOwned ⟨store.funcs.length,store.externs.length⟩ value) :
    ReferenceShape store ty word := by
  cases value with
  | CONST type bits => cases type <;> cases ty <;> simp [Compiler.valueType,sourceType,valtype_numtype,numtype_Inn,numtype_Fnn] at typed
  | VCONST type bits => cases ty <;> simp [Compiler.valueType,sourceType] at typed
  | REF_NULL type =>
    exact Or.inl (by simpa [Compiler.encodeValue] using represented)
  | REF_FUNC_ADDR address =>
    cases ty with
    | FuncRef =>
      apply Or.inr
      simpa [represented,Compiler.encodeValue,SourceMachine.Ownership.ValueOwned] using owned
    | ExternRef => simp [Compiler.valueType,sourceType] at typed
  | REF_HOST_ADDR address =>
    cases ty with
    | FuncRef => simp [Compiler.valueType,sourceType] at typed
    | ExternRef =>
      apply Or.inr
      simpa [represented,Compiler.encodeValue,SourceMachine.Ownership.ValueOwned] using owned

theorem global_encoded_shape {M : Type} (store : runtime.store.Store M)
    (old : runtime.store.GlobalInst) (lo hi : U64) (value : val)
    (prior : GlobalShape store old) (wellFormed : wf_val value)
    (typed : sourceType old.ty.valtype = Compiler.valueType value)
    (represented : pairWords old.ty.valtype (lo,hi) = Compiler.encodeValue value)
    (high : old.ty.valtype ≠ .V128 → hi = old.hi)
    (owned : SourceMachine.Ownership.ValueOwned ⟨store.funcs.length,store.externs.length⟩ value) :
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
    exact encode_value_f32_low value wellFormed (by simpa [kind,sourceType] using typed.symm)
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
    (owned : SourceMachine.Ownership.ValueOwned ⟨before.funcs.length,before.externs.length⟩ value) :
    Shape view after := by
  obtain ⟨index,old,lo,hi,found,mutable,typed,represented,high,rfl⟩ := mutation
  apply shape.global_replace
  exact global_encoded_shape before old lo hi value (shape.globals old (List.mem_of_getElem? found))
    wellFormed typed represented high owned
end Itasca.Runtime.Store

end

/-! ## BulkResult -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

def statefulBulkResult {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : SourceMachine.AResult :=
  match out.1 with
  | .Ok _ => SourceMachine.advance {state with store := decodeStore view code out.2} {f with code := after,vals := front} rest
  | .Err _ => .trap

theorem bulk_integer_decoded (word : U64) :
    SourceMachine.integer .I32 (SourceMachine.integerVal .I32 (bulkWord word).val) = some (bulkWord word).val :=
  SourceMachine.integer_accepts .I32 _ (by change (bulkWord word).val < 2^32; simp only [bulkWord,U32.cast_U64_val_eq]; scalar_tac)
end Itasca.Runtime.Integration

end
