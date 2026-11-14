import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Store.Api.ApiMetadata
import Itasca.Runtime.Store.Invariant.Rollback
import Itasca.Runtime.Spec.Integer

/-!
Sections, each formerly its own module: ForeignValues, IssuedValues, CheckedValues, CanonicalSignatures, HostSignature.
-/

/-! ## ForeignValues -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A reference value whose private handle belongs to another store. Numeric
values and null references are never foreign. -/
def ForeignValue {M : Type} (s : runtime.store.Store M) : runtime.Value → Prop
  | .FuncRef (some a) => a.store ≠ s.id
  | .ExternRef (some a) => a.store ≠ s.id
  | _ => False

end Itasca.Runtime.Store

end

/-! ## IssuedValues -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A public value is either owned by this store or carries a foreign store
identity. Same-store references must denote an issued address. -/
def IssuedValue {M : Type} (s : runtime.store.Store M) (value : runtime.Value) : Prop :=
  match value with
  | .FuncRef (some address) => address.store = s.id → address.index.val < s.funcs.length
  | .ExternRef (some address) => address.store = s.id → address.index.val < s.externs.length
  | _ => True

/-- Issued same-store values satisfy all actual slot-encoding bounds. -/
theorem issued_value_owned_or_foreign {M : Type} (s : runtime.store.Store M)
    (value : runtime.Value) (issued : IssuedValue s value) :
    ValueInStore s value ∨ ForeignValue s value := by
  cases value <;> simp only [IssuedValue, ValueInStore, ForeignValue, Interp.ValueOwnedFits] at issued ⊢
  all_goals try { exact Or.inl ⟨trivial, trivial⟩ }
  all_goals rename_i address
  all_goals cases address with
  | none => exact Or.inl ⟨trivial, trivial⟩
  | some address =>
    by_cases same : address.store = s.id
    · have bound := issued same
      left
      refine ⟨⟨same, ?_, ?_⟩, bound⟩
      · scalar_tac
      · rcases Usize.bounds_eq with h | h <;> scalar_tac
    · exact Or.inr same

end Itasca.Runtime.Store

end

/-! ## CheckedValues -/

section

/-!
Issued-value checking, decoded source typing and argument ownership. The lightweight IssuedValue contract remains independently available.
-/

/-! ## Checked Values -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

/-- Ownership checks plus issued-address provenance imply the full value
invariant used by encoding and source typing. -/
theorem IssuedValue.in_store {M : Type} {s : runtime.store.Store M} {value : runtime.Value}
    (issued : IssuedValue s value) (owner : Interp.OwnedBy s.id value) : ValueInStore s value := by
  rcases issued_value_owned_or_foreign s value issued with owned | foreign
  · exact owned
  · cases value <;> simp only [ForeignValue, Interp.OwnedBy] at foreign owner
    all_goals rename_i address
    all_goals cases address with
    | none => contradiction
    | some address => exact False.elim (foreign owner)

/-- Pointwise checked tags and ownership give typed source results. -/
theorem matched_issued_source_typed {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (store : runtime.store.Store M)
    (sourceWf : wf_store (decodeStore view code store))
    {values : List runtime.Value} {types : List Itasca.wasm_types.ValueType}
    (matched : List.Forall₂ (Interp.ArgumentMatches store.id) values types)
    (issued : ∀ value ∈ values, IssuedValue store value) :
    ResultsTyped (decodeStore view code store) (types.map Interp.sourceType)
      (values.map Interp.sourceValue) ∧
    (∀ value ∈ values, ValueInStore store value) ∧ types = values.map Interp.rawType := by
  revert issued
  induction matched with
  | nil => intro issued; exact ⟨.nil, by simp, rfl⟩
  | @cons value ty values types matching tail ih =>
    intro issued
    have head := (issued value (by simp)).in_store matching.1
    obtain ⟨typed, owned, tags⟩ := ih (fun value member => issued value (by simp [member]))
    refine ⟨List.Forall₂.cons ?_ typed, ?_, ?_⟩
    · rw [← matching.2]
      exact value_in_store_typed view code store sourceWf value head
    · intro v member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact owned v member
    · simp only [List.map_cons, matching.2, tags]

/-- The concrete value checker establishes specification result typing from
issued values; it does not assume the host returned correctly typed results. -/
theorem check_values_source_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation) (store : runtime.store.Store M)
    (sourceWf : wf_store (decodeStore view code store))
    (values : Slice runtime.Value) (types : Slice Itasca.wasm_types.ValueType)
    (issued : ∀ value ∈ values.val, IssuedValue store value) :
    runtime.interp.check_values memory store values types ⦃ status =>
      status = .Ok () →
        ResultsTyped (decodeStore view code store) (types.val.map Interp.sourceType)
          (values.val.map Interp.sourceValue) ∧
        (∀ value ∈ values.val, ValueInStore store value) ∧
        types.val = values.val.map Interp.rawType ⦄ := by
  step with Interp.check_values_accepts_iff memory store values types as ⟨status, accepted⟩
  rename_i success
  exact matched_issued_source_typed view code store sourceWf (accepted.mp success) issued
end Itasca.Runtime.Store

end

/-! ## Issued Arguments -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem ValueInStore.issued {M : Type} {store : runtime.store.Store M} {value : runtime.Value}
    (valid : ValueInStore store value) : IssuedValue store value := by
  cases value <;> simp only [IssuedValue,ValueInStore] at valid ⊢
  all_goals cases ‹Option _› <;> simp_all

/-- Ownership is obtained from the actual argument checker; foreign issued
references remain admissible inputs to the public rejection theorem. -/
theorem checked_arguments_owned {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation) (store : runtime.store.Store M)
    (sourceWf : wf_store (decodeStore view code store))
    (args : Slice runtime.Value) (types : Slice Itasca.wasm_types.ValueType)
    (issued : ∀ value ∈ args.val, IssuedValue store value)
    (accepted : runtime.interp.check_values memory store args types = .ok (.Ok ())) :
    ∀ value ∈ args.val, ValueInStore store value := by
  have checked := check_values_source_typed memory view code store sourceWf args types issued
  rw [accepted,WP.spec_ok] at checked
  exact (checked rfl).2.1
end Itasca.Runtime.Store

end

end

/-! ## CanonicalSignatures -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Interned indices agree exactly when their source signatures agree. -/
theorem Shape.signature_eq_iff {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Shape view store)
    (left right : Usize) (leftType rightType : Itasca.wasm_types.FuncType)
    (leftFound : store.types.val[left.val]? = some leftType)
    (rightFound : store.types.val[right.val]? = some rightType) :
    left = right ↔ decodeFuncType leftType = decodeFuncType rightType := by
  constructor
  · intro same
    subst right
    have sameType : leftType = rightType := Option.some.inj (leftFound.symm.trans rightFound)
    exact congrArg decodeFuncType sameType
  · intro same
    have leftBound := (List.getElem?_eq_some_iff.mp leftFound).1
    have rightBound := (List.getElem?_eq_some_iff.mp rightFound).1
    have leftEq := (List.getElem?_eq_some_iff.mp leftFound).2
    have rightEq := (List.getElem?_eq_some_iff.mp rightFound).2
    have eq : (store.types.val.map decodeFuncType)[left.val]'(by simpa using leftBound) =
        (store.types.val.map decodeFuncType)[right.val]'(by simpa using rightBound) := by
      simpa only [List.getElem_map,leftEq,rightEq] using same
    have indices := shape.canonicalTypes.getElem_inj_iff.mp eq
    exact UScalar.eq_of_val_eq indices

/-- The runtime signature check is the source function-type check, including
functions imported from other instances. -/
theorem Shape.function_signature_eq_iff {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Shape view store)
    (code : CodeInterpretation) (function : runtime.store.FuncInst)
    (present : function ∈ store.funcs.val) (wanted : Usize)
    (wantedType : Itasca.wasm_types.FuncType)
    (wantedFound : store.types.val[wanted.val]? = some wantedType) :
    function.signature = wanted ↔
      (decodeFunction code store function).TYPE = decodeFuncType wantedType := by
  have bound := (shape.functions function present).1
  have actualFound : store.types.val[function.signature.val]? =
      some store.types.val[function.signature.val] := List.getElem?_eq_getElem bound
  have actualType : (decodeFunction code store function).TYPE =
      decodeFuncType store.types.val[function.signature.val] := by
    unfold decodeFunction
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,actualFound,
      Option.map_some,Option.getD_some]
    cases function.code with
    | Host id => rfl
    | Wasm inst fn => dsimp only; split <;> rfl
  rw [actualType]
  exact shape.signature_eq_iff function.signature wanted _ wantedType actualFound wantedFound

/-- Function references in a shaped table fit the machine index width, even
when the reference word is wider than `usize`. -/
theorem Shape.table_function_reference_cast {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Shape view store)
    (table : runtime.store.TableInst) (present : table ∈ store.tables.val)
    (funcref : table.ty = .FuncRef) (position : Nat) (reference : U64)
    (selected : table.elements.val[position]? = some reference) :
    (UScalar.cast .Usize reference).val = reference.val := by
  have owned := (shape.tables table present).2.2 reference (List.mem_of_getElem? selected)
  rw [funcref] at owned
  have bound : reference.val ≤ store.funcs.length := by
    rcases owned with zero | positive
    · omega
    · dsimp only at positive
      omega
  have fits : reference.val < 2 ^ UScalarTy.Usize.numBits := by
    have capacity := store.funcs.property
    scalar_tac
  simp only [UScalar.cast_val_eq,Nat.mod_eq_of_lt fits]

/-- A nonnull funcref retained in a shaped table selects an actual function. -/
theorem Shape.table_function_target {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Shape view store)
    (table : runtime.store.TableInst) (present : table ∈ store.tables.val)
    (funcref : table.ty = .FuncRef) (position : Nat) (reference : U64)
    (selected : table.elements.val[position]? = some reference)
    (nonzero : reference ≠ 0#u64) :
    ∃ address : Usize, ∃ function : runtime.store.FuncInst,
      (UScalar.cast .Usize reference).val = address.val+1 ∧
      store.funcs.val[address.val]? = some function := by
  have owned := (shape.tables table present).2.2 reference (List.mem_of_getElem? selected)
  rw [funcref] at owned
  have positive : reference.val ≠ 0 := by intro h; apply nonzero; scalar_tac
  have bound : reference.val-1 < store.funcs.length := by simpa [ReferenceShape,positive] using owned
  have refBound : reference.val < 2 ^ UScalarTy.Usize.numBits := by
    have capacity := store.funcs.property
    scalar_tac
  let address : Usize := UScalar.ofNatCore (reference.val-1) (by omega)
  refine ⟨address,store.funcs.val[reference.val-1],?_,?_⟩
  · dsimp only [address]
    simp only [UScalar.cast_val_eq,UScalar.ofNatCore_val_eq,Nat.mod_eq_of_lt refBound]
    omega
  · exact List.getElem?_eq_getElem bound

end Itasca.Runtime.Store

end

/-! ## HostSignature -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- An issued raw host entry decodes to the host identity and its exact signature. -/
theorem decode_host_function {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (identity : U64) (signature : Itasca.wasm_types.FuncType)
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
    (function : runtime.store.FuncInst) (signature : Itasca.wasm_types.FuncType)
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
      decode_function_type code before function oldSigBound,
      decode_function_type code after nextFunction sigBound,oldSigEqual,nextSigEqual] using equal
  have same := decode_func_type_injective decoded
  exact ⟨nextFunction,nextFound,by rw [←same]; exact nextSig⟩
end Itasca.Runtime.Store

end
