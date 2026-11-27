import Itasca.Results.Definitions.Store.Read
import Itasca.Results.Definitions.Store.Mutation
import Itasca.Results.Definitions.Instantiation
import Itasca.Results.Definitions.Invocation

/-!
# The runtime capability contract

Start here when composing runtime API calls. The checked runtime_verified theorem
supplies one predicate Inv and these capabilities. Choose it once and retain it
across store operations and callbacks; it is not an embedding assumption.

The operation laws live beside their semantic vocabulary in Store/Read,
Store/Mutation, Instantiation and Invocation. Host states the callback obligations.
Each public theorem requires only its relevant capability; RuntimeContract joins
them under the same predicate.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Representation Itasca.Interp Itasca.Store

/-- Construction and mutation laws for one shared store predicate. -/
structure StoreMutationContract {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop where
  well_formed : Store.WellFormedLaw view Inv
  source_typed : Store.SourceTypedLaw view Inv
  with_identity : Store.WithIdentityLaw view Inv
  define_extern_with : Store.DefineExternWithLaw view Inv
  define_host_with : Store.DefineHostWithLaw view Inv
  define_memory_with : Store.DefineMemoryWithLaw view Inv
  define_table_with : Store.DefineTableWithLaw view Inv
  define_global_with : Store.DefineGlobalWithLaw view Inv
  set_global : Store.SetGlobalLaw view Inv
  set_table : Store.SetTableLaw view Inv
  memory_mut : Store.MemoryMutLaw view Inv
  grow_memory_with : Store.GrowMemoryWithLaw view Inv
  grow_table_with : Store.GrowTableWithLaw view Inv

/-- Read-only observations of a store, independent of instantiation and invocation laws. -/
structure StoreReadContract {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop where
  global : Store.GlobalLaw view Inv
  memory : Store.MemoryLaw view Inv
  table_size : Store.TableSizeLaw view Inv
  table_get : Store.TableGetLaw view Inv
  func_type : Store.FuncTypeLaw view Inv
  extern_identity : Store.ExternIdentityLaw view Inv
  export_lookup : Store.ExportLookupLaw view Inv

/-- Linking and initialization of accepted compiled modules under the shared store predicate. -/
structure InstantiationContract {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop where
  instantiate : InstantiationLaw view Inv

/-- Invocation behavior under the shared store predicate. -/
structure InvocationContract {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop where
  behaves : InvocationLaw view Inv

/-- Resource completeness under the same store predicate as ordinary behavior. -/
structure InvocationResourceContract {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop where
  resource_complete : InvocationResourceLaw view Inv

/-- One predicate supports all API capabilities. The checked existence theorem
supplies this bundle; individual operations require only their own capability.
Keep the same predicate when composing operations and host callbacks. -/
structure RuntimeContract {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop
    extends StoreMutationContract view Inv, StoreReadContract view Inv,
      InstantiationContract view Inv, InvocationContract view Inv, InvocationResourceContract view Inv
end Itasca.Integration
