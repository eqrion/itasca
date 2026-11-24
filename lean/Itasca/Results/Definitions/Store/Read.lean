import Itasca.Results.Definitions.Store.State

/-!
# Store reads and export lookup

Read-only API guarantees over issued handles. These laws expose decoded values,
bytes, signatures and exports, and preserve the chosen store predicate.
Construction and mutation laws live in Mutation.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std SpecExt Itasca.Representation Itasca.Integration

/-- Global reads return the value in the decoded global component. -/
def GlobalLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.GlobalAddr) (_issued : ExternalIssued store (.Global address)) ,
  runtime.store.Store.global memory store address ⦃ result =>
    RustResult.Post result
      (onError := fun error =>
        error = .WrongStore ∧ address.store ≠ store.id)
      (onSuccess := fun value =>
        address.store = store.id ∧ ∃ object : globalinst,
        (decodeStore view code store).GLOBALS[address.index.val]? = some object ∧
        ValueInStore store value ∧ sourceValue value = object.VALUE ∧
        ∃ mutability, object.TYPE = .mk_globaltype mutability (Representation.valueType (sourceValue value))) ⦄

/-- A memory read exposes the platform view of the decoded memory bytes. -/
def MemoryLaw {M : Type} (view : M → Slice U8)
    (_Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M)
  (_memory_laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
  (store : runtime.store.Store M) (address : runtime.MemoryAddr)
  (_issued : ExternalIssued store (.Memory address)) ,
  runtime.store.Store.memory memory store address ⦃ result =>
    RustResult.Post result
      (onError := fun error =>
        error = .WrongStore ∧ address.store ≠ store.id)
      (onSuccess := fun bytes =>
        address.store = store.id ∧ ∃ object : meminst,
        (decodeStore view code store).MEMS[address.index.val]? = some object ∧
        object.BYTES = decodeBytes bytes.val) ⦄

/-- Table size is the length of the decoded reference vector. -/
def TableSizeLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.TableAddr) (_issued : ExternalIssued store (.Table address)) ,
  runtime.store.Store.table_size memory store address ⦃ result =>
    RustResult.Post result
      (onError := fun error =>
        error = .WrongStore ∧ address.store ≠ store.id)
      (onSuccess := fun size =>
        address.store = store.id ∧ ∃ object : tableinst,
        (decodeStore view code store).TABLES[address.index.val]? = some object ∧ size.val = object.REFS.length) ⦄

/-- Table reads expose exactly the selected decoded reference, or report the
  checked element bound separately from a foreign table handle. -/
def TableGetLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.TableAddr) (index : U32) (_issued : ExternalIssued store (.Table address)) ,
  runtime.store.Store.table_get memory store address index ⦃ result =>
    RustResult.Post result
      (onError := fun error =>
        (error = .WrongStore ∧ address.store ≠ store.id) ∨
        (error = .Trap .TableOutOfBounds ∧ address.store = store.id ∧ ∃ object : tableinst,
          (decodeStore view code store).TABLES[address.index.val]? = some object ∧ object.REFS.length ≤ index.val))
      (onSuccess := fun value =>
        address.store = store.id ∧ ∃ object : tableinst, ∃ reference,
        (decodeStore view code store).TABLES[address.index.val]? = some object ∧
        object.REFS[index.val]? = some reference ∧
        ValueInStore store value ∧ sourceValue value = val_ref reference) ⦄

/-- Function type lookup returns the decoded type of the issued function. -/
def FuncTypeLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.FuncAddr) (_issued : ExternalIssued store (.Func address)) ,
  runtime.store.Store.func_type memory store address ⦃ result =>
    RustResult.Post result
      (onError := fun error =>
        error = .WrongStore ∧ address.store ≠ store.id)
      (onSuccess := fun signature =>
        address.store = store.id ∧ ∃ function : funcinst,
        (decodeStore view code store).FUNCS[address.index.val]? = some function ∧
        function.TYPE = Itasca.Translation.Environment.funcType signature) ⦄

/-- External identities are the exact values retained at the issued address. -/
def ExternIdentityLaw {M : Type} (_view : M → Slice U8)
    (_Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
  (address : runtime.ExternAddr) (_issued : IssuedValue store (.ExternRef (some address))) ,
  runtime.store.Store.extern_identity memory store address ⦃ result =>
    RustResult.Post result
      (onError := fun error =>
        error = .WrongStore ∧ address.store ≠ store.id)
      (onSuccess := fun identity =>
        address.store = store.id ∧ store.externs.val[address.index.val]? = some identity) ⦄

/-- Export lookup matches exact byte names. Returned handles are
  owned by the store and agree with decoded exports, including for arbitrary query bytes. -/
def ExportLookupLaw {M : Type} (_view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.InstanceAddr) (query : Slice U8)
  (_index_if_owned : address.store = store.id → address.index.val < store.instances.length) ,
  runtime.store.Store.export memory store address query ⦃ result =>
    RustResult.Post result
      (onError := fun error =>
        error = .WrongStore ∧ address.store ≠ store.id)
      (onSuccess := fun found =>
        address.store = store.id ∧ ∃ inst,
        store.instances.val[address.index.val]? = some inst ∧
        (found = none ↔ ∀ entry ∈ inst.module.module.env.exports.val, entry.name.val ≠ query.val) ∧
        ∀ external, found = some external →
          ExternalInStore store external ∧ ExportMatches inst query external) ⦄

end Itasca.Store
