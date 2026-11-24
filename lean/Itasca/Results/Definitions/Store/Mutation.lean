import Itasca.Results.Definitions.Store.State

/-!
# Store construction and mutation

Each law states its input obligations, exact source effect, and failure behavior.
All operations use the same chosen store predicate. Read-only laws live in Read;
Runtime bundles the capabilities without adding assumptions.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std SpecExt Itasca.Representation Itasca.Integration

/-- Every admitted store decodes to a well-formed source store. -/
def WellFormedLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store, Inv code store → wf_store (decodeStore view code store)

/-- Source typing is available to callbacks that retain or extend the store. -/
def SourceTypedLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store, Inv code store → Store_ok (decodeStore view code store)

/-- An empty store has the store predicate for every code interpretation.
  The native wrapper supplies the positive identity: its counter starts at one
  and advances with checked addition. That wrapper is outside extraction. -/
def WithIdentityLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M)
  (code : Representation.CodeInterpretation) (id : Usize) (limits : runtime.store.StoreLimits)
  (_positive : 0 < id.val) ,
  runtime.store.Store.with_identity memory id limits ⦃ store =>
    Inv code store ∧ store.id = id ∧ store.limits = limits ∧
      Representation.decodeStore view code store = ⟨[], [], [], [], [], []⟩ ⦄

/-- Defining an external identity preserves the store predicate and the decoded
  source store. Failure leaves the store unchanged; success appends one owned identity. -/
def DefineExternWithLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {A : Type}
  (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
  (_allocator_correct : Platform.AllocCorrect allocator) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store) (identity : U64) ,
  runtime.store.Store.define_extern_with memory allocator store identity ⦃ (result, after) =>
    Inv code after ∧ Store.MetadataPreserved store after ∧
    after.limits = store.limits ∧ decodeStore view code after = decodeStore view code store ∧
    RustResult.Post result
      (onError := fun _ =>
        after = store)
      (onSuccess := fun address =>
        address.store = store.id ∧ address.index.val = store.externs.length ∧
        ValueInStore after (.ExternRef (some address)) ∧
        ∃ externs : alloc.vec.Vec U64, externs.val = store.externs.val ++ [identity] ∧
          after = {store with externs}) ⦄

/-- A host definition either leaves the store unchanged or appends an issued
  host with its exact structural signature, preserving the store predicate. -/
def DefineHostWithLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {A : Type}
  (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
  (_allocator_correct : Platform.AllocCorrect allocator) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (ty : Itasca.wasm_types.FuncType) (host : U64) ,
  runtime.store.Store.define_host_with memory allocator store ty host ⦃ (result, after) =>
    Inv code after ∧ Store.MetadataExtended store after ∧
    after.externs = store.externs ∧ after.limits = store.limits ∧
    SourceStorePrefix (decodeStore view code store) (decodeStore view code after) ∧
    Extend_store (decodeStore view code store) (decodeStore view code after) ∧
    RustResult.Post result
      (onError := fun _ =>
        after = store)
      (onSuccess := fun address =>
        address.store = store.id ∧ address.index.val = store.funcs.length ∧
        ExternalIssued after (.Func address) ∧ ValueInStore after (.FuncRef (some address)) ∧
        SpecExt.HostFunction (decodeStore view code after) address.index.val host.val
          (ty.params.val.map Itasca.Translation.valueType) (ty.results.val.map Itasca.Translation.valueType)) ⦄

/-- Defining memory retains the supplied buffer bytes, establishes the declared
  page bounds, and preserves the admitted store. Every failure is atomic. -/
def DefineMemoryWithLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {A : Type}
  (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
  (_allocator_correct : Platform.AllocCorrect allocator)
  (_memory_laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (ty : Itasca.wasm_types.MemType) (buffer : M) ,
  runtime.store.Store.define_memory_with memory allocator store ty buffer ⦃ (result, after) =>
    Inv code after ∧ StoreMutation view code store after ∧
    RustResult.Post result
      (onError := fun _ =>
        after = store)
      (onSuccess := fun address =>
        address.store = store.id ∧ address.index.val = store.memories.length ∧
        ExternalIssued after (.Memory address) ∧
        (decodeStore view code after).MEMS = (decodeStore view code store).MEMS ++
          [⟨.PAGE (decodeLimits ty.limits.min.val ty.limits.max),decodeBytes (view buffer).val⟩] ∧
        (view buffer).length = ty.limits.min.val * 65536) ⦄

/-- Defining a table appends exactly the declared number of null references;
  all rejection and allocation failures leave the original store unchanged. -/
def DefineTableWithLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {A : Type}
  (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
  (_allocator_correct : Platform.AllocCorrect allocator) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (ty : Itasca.wasm_types.TableType) ,
  runtime.store.Store.define_table_with memory allocator store ty ⦃ (result, after) =>
    Inv code after ∧ StoreMutation view code store after ∧
    RustResult.Post result
      (onError := fun _ =>
        after = store)
      (onSuccess := fun address =>
        address.store = store.id ∧ address.index.val = store.tables.length ∧
        ExternalIssued after (.Table address) ∧
        (decodeStore view code after).TABLES = (decodeStore view code store).TABLES ++
          [⟨.mk_tabletype (decodeLimits ty.limits.min.val ty.limits.max) (Itasca.Translation.referenceType ty.elem),
            List.replicate ty.limits.min.val (.REF_NULL (Itasca.Translation.referenceType ty.elem))⟩]) ⦄

/-- A global definition accepts only an owned value of its declared type.
  Success appends the exact decoded value; every rejection preserves the store. -/
def DefineGlobalWithLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {A : Type}
  (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
  (_allocator_correct : Platform.AllocCorrect allocator) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (ty : Itasca.wasm_types.GlobalType) (value : runtime.Value) (_issued : IssuedValue store value) ,
  runtime.store.Store.define_global_with memory allocator store ty value ⦃ (result, after) =>
    Inv code after ∧ StoreMutation view code store after ∧
    RustResult.Post result
      (onError := fun _ =>
        after = store)
      (onSuccess := fun address =>
        address.store = store.id ∧ address.index.val = store.globals.length ∧
        ExternalIssued after (.Global address) ∧ ty.valtype = Representation.rawType value ∧
        (decodeStore view code after).GLOBALS = (decodeStore view code store).GLOBALS ++
          [⟨.mk_globaltype (Itasca.Translation.mutability ty.mutability) (Itasca.Translation.valueType ty.valtype),
            Representation.sourceValue value⟩]) ⦄

/-- Setting an issued mutable global writes the requested address and exact
  source value. Foreign, immutable, and mistyped writes leave the store unchanged. -/
def SetGlobalLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.GlobalAddr) (value : runtime.Value)
  (_issued : ExternalIssued store (.Global address)) (_value_issued : IssuedValue store value) ,
  runtime.store.Store.set_global memory store address value ⦃ (result, after) =>
    Inv code after ∧ StoreMutation view code store after ∧
    RustResult.Post result
      (onError := fun _ =>
        after = store)
      (onSuccess := fun _ =>
        GlobalUpdate (decodeStore view code store) (decodeStore view code after)
          address.index.val (sourceValue value)) ⦄

/-- Setting a table updates exactly the issued table and requested element.
  All ownership, type, and bounds rejections leave the store unchanged. -/
def SetTableLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.TableAddr) (index : U32) (value : runtime.Value)
  (_issued : ExternalIssued store (.Table address)) (_value_issued : IssuedValue store value) ,
  runtime.store.Store.set_table memory store address index value ⦃ (result, after) =>
    Inv code after ∧ StoreMutation view code store after ∧
    RustResult.Post result
      (onError := fun _ =>
        after = store)
      (onSuccess := fun _ =>
        TableUpdate (decodeStore view code store) (decodeStore view code after)
          address.index.val index.val (sourceValue value)) ⦄

/-- Mutable memory borrowing preserves the store predicate when the caller
  writes back the same number of bytes. Successful borrowing relates that slice
  to decoded memory; error write-back retains the executable and mutation certificates. -/
def MemoryMutLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M)
  (_memory_laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.MemoryAddr) (_issued : ExternalIssued store (.Memory address)) ,
  runtime.store.Store.memory_mut memory store address ⦃ (result, back) =>
    RustResult.Post result
      (onError := fun error =>
        error = .WrongStore ∧ address.store ≠ store.id ∧
        ∀ reply, Inv code (back reply) ∧
          StoreMutation view code store (back reply) ∧ back reply = store)
      (onSuccess := fun bytes =>
        ∃ object : meminst,
        address.store = store.id ∧ (decodeStore view code store).MEMS[address.index.val]? = some object ∧
        decodeBytes bytes.val = object.BYTES ∧
        (∀ replacement : Slice U8, replacement.length = bytes.length →
          Inv code (back (.Ok replacement)) ∧
          StoreMutation view code store (back (.Ok replacement)) ∧
          MemoryUpdate (decodeStore view code store) (decodeStore view code (back (.Ok replacement)))
            address.index.val (decodeBytes replacement.val)) ∧
        ∀ error, Inv code (back (.Err error)) ∧
          StoreMutation view code store (back (.Err error))) ⦄

/-- Memory growth preserves admitted stores, including the failure sentinel. -/
def GrowMemoryWithLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀
  (memory : runtime.platform.MemoryBuffer M)
  (_memory_laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.MemoryAddr) (delta : U32)
  (_issued : ExternalIssued store (.Memory address)) ,
  runtime.store.Store.grow_memory_with memory store address delta ⦃ (result, after) =>
    Inv code after ∧ StoreMutation view code store after ∧
    RustResult.Post result
      (onError := fun error =>
        error = .WrongStore ∧ address.store ≠ store.id ∧ after = store)
      (onSuccess := fun pages =>
        address.store = store.id ∧
          MemoryGrown (decodeStore view code store) (decodeStore view code after)
            address.index.val delta.val pages.val ∧
          ((decodeStore view code after).MEMS.map fun object => object.BYTES.length).sum ≤
            store.limits.max_memory_bytes.val) ⦄

/-- Table growth checks ownership and reference type before extending the table. -/
def GrowTableWithLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {A : Type}
  (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
  (_allocator_correct : Platform.AllocCorrect allocator) (code : CodeInterpretation)
  (store : runtime.store.Store M) (_store_invariant : Inv code store)
  (address : runtime.TableAddr) (delta : U32) (value : runtime.Value)
  (_issued : ExternalIssued store (.Table address)) (_value_issued : IssuedValue store value) ,
  runtime.store.Store.grow_table_with memory allocator store address delta value ⦃ (result, after) =>
    Inv code after ∧ StoreMutation view code store after ∧
    RustResult.Post result
      (onError := fun error =>
        after = store ∧ (error = .WrongStore ∨ error = .BadArguments))
      (onSuccess := fun size =>
        address.store = store.id ∧
          TableGrown (decodeStore view code store) (decodeStore view code after)
            address.index.val delta.val size.val (sourceValue value) ∧
          ((decodeStore view code after).TABLES.map fun object => object.REFS.length).sum ≤
            store.limits.max_table_elements.val) ⦄

end Itasca.Store
