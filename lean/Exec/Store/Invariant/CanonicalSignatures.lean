import Exec.Representation.StoreInvariant

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Interned indices agree exactly when their source signatures agree. -/
theorem Shape.signature_eq_iff {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Shape view store)
    (left right : Usize) (leftType rightType : Itasca.types.FuncType)
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
    (code : CodeInterpretation) (function : runtime.store.Function)
    (present : function ∈ store.funcs.val) (wanted : Usize)
    (wantedType : Itasca.types.FuncType)
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
    (table : runtime.store.Table) (present : table ∈ store.tables.val)
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
    (table : runtime.store.Table) (present : table ∈ store.tables.val)
    (funcref : table.ty = .FuncRef) (position : Nat) (reference : U64)
    (selected : table.elements.val[position]? = some reference)
    (nonzero : reference ≠ 0#u64) :
    ∃ address : Usize, ∃ function : runtime.store.Function,
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

end Exec.Store
