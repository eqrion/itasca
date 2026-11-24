import Itasca.Results.Definitions.Runtime
import Itasca.Runtime.Integration.RuntimeContract

open Itasca.Representation

/-!
# Store API

An empty store starts with the chosen store predicate under a positive identity.
Definitions, writes, and growth preserve it under their explicit allocation,
memory, handle, and value premises. Reads agree with the retained objects and
their decoded source representations. Export lookup compares exact raw bytes.

These contracts describe ordinary Rust errors as well as success. Mutable
memory write-back requires the original byte length. Native identity issuance
and platform implementations remain subject to the obligations described in
[Platform](Definitions/Platform.lean).
-/

open Aeneas Aeneas.Std SpecExt

namespace Itasca
open Integration Interp Store

/-- The checked implementation supplies one store predicate with all public
API laws. Choose it once, then use it consistently for stores and host callbacks.
Its construction is internal; the capability laws in Definitions/Integration
state its complete public meaning. Each operation below references its single
canonical law there. -/
theorem Integration.runtime_verified {M : Type} (view : M → Slice U8) :
    ∃ Inv, RuntimeContract view Inv := runtime_contract_exists view

/-- An empty store has the chosen store predicate for every code interpretation.
The native wrapper supplies the positive identity: its counter starts at one
and advances with checked addition. That wrapper is outside extraction. -/
theorem Store.with_identity.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.WithIdentityLaw view Inv :=
  contract.with_identity

/-- Defining an external identity preserves store metadata and the decoded
source store. Failure leaves the store unchanged; success appends one owned identity. -/
theorem Store.define_extern_with.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.DefineExternWithLaw view Inv :=
  contract.define_extern_with

/-- A host definition either leaves the store unchanged or appends an issued
host with its exact structural signature, preserving the chosen store predicate. -/
theorem Store.define_host_with.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.DefineHostWithLaw view Inv :=
  contract.define_host_with

/-- Defining memory retains the supplied buffer bytes, establishes the declared
page bounds, and preserves the admitted store. Every failure is atomic. -/
theorem Store.define_memory_with.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.DefineMemoryWithLaw view Inv :=
  contract.define_memory_with

/-- Defining a table appends exactly the declared number of null references;
all rejection and allocation failures leave the original store unchanged. -/
theorem Store.define_table_with.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.DefineTableWithLaw view Inv :=
  contract.define_table_with

/-- A global definition accepts only an owned value of its declared type.
Success appends the exact decoded value; every rejection preserves the store. -/
theorem Store.define_global_with.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.DefineGlobalWithLaw view Inv :=
  contract.define_global_with

/-- Setting an issued mutable global writes the requested address and exact
source value. Foreign, immutable, and mistyped writes leave the store unchanged. -/
theorem Store.set_global.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.SetGlobalLaw view Inv :=
  contract.set_global

/-- Setting a table updates exactly the issued table and requested element.
All ownership, type, and bounds rejections leave the store unchanged. -/
theorem Store.set_table.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.SetTableLaw view Inv :=
  contract.set_table

/-- Mutable memory borrowing preserves the chosen store predicate when the caller
writes back the same number of bytes. Successful borrowing relates that slice
to decoded memory; error write-back retains the executable and mutation certificates. -/
theorem Store.memory_mut.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.MemoryMutLaw view Inv :=
  contract.memory_mut

/-- Memory growth preserves admitted stores, including the failure sentinel. -/
theorem Store.grow_memory_with.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.GrowMemoryWithLaw view Inv :=
  contract.grow_memory_with

/-- Table growth checks ownership and reference type before extending the table. -/
theorem Store.grow_table_with.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreMutationContract view Inv) : Store.GrowTableWithLaw view Inv :=
  contract.grow_table_with

/-- Global reads return the value in the decoded global component. -/
theorem Store.global.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreReadContract view Inv) : Store.GlobalLaw view Inv :=
  contract.global

/-- A memory read exposes the platform view of the decoded memory bytes. -/
theorem Store.memory.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreReadContract view Inv) : Store.MemoryLaw view Inv :=
  contract.memory

/-- Table size is the length of the decoded reference vector. -/
theorem Store.table_size.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreReadContract view Inv) : Store.TableSizeLaw view Inv :=
  contract.table_size

/-- Table reads expose exactly the selected decoded reference, or report the
checked element bound separately from a foreign table handle. -/
theorem Store.table_get.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreReadContract view Inv) : Store.TableGetLaw view Inv :=
  contract.table_get

/-- Function type lookup returns the decoded type of the issued function. -/
theorem Store.func_type.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreReadContract view Inv) : Store.FuncTypeLaw view Inv :=
  contract.func_type

/-- External identities are the exact values retained at the issued address. -/
theorem Store.extern_identity.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (address : runtime.ExternAddr) (issued : IssuedValue store (.ExternRef (some address))) :
    runtime.store.Store.extern_identity memory store address ⦃ result =>
      RustResult.Post result
        (onError := fun error =>
          error = .WrongStore ∧ address.store ≠ store.id)
        (onSuccess := fun identity =>
          address.store = store.id ∧ store.externs.val[address.index.val]? = some identity) ⦄ := by
  apply Aeneas.Std.WP.spec_mono (_root_.Itasca.runtime.store.Store.extern_identity.spec memory store address issued)
  intro result held
  cases result <;> simpa only [uncurry_apply_pair, RustResult.Post] using held

/-- Export lookup matches exact byte names. Returned handles are
owned by the store and agree with decoded exports, including for arbitrary query bytes. -/
theorem Store.export.spec {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : StoreReadContract view Inv) : Store.ExportLookupLaw view Inv :=
  contract.export_lookup

end Itasca
