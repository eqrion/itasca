import Itasca.Runtime.Integration.Api.StoreCreate
import Itasca.Runtime.Integration.Api.StoreDefine
import Itasca.Runtime.Integration.Api.StoreWrite
import Itasca.Runtime.Integration.Api.StoreGrow
import Itasca.Runtime.Integration.Api.StoreRead

/-!
# Store API

An empty store starts with the executable invariant under a positive identity.
Definitions, writes, and growth preserve it under their explicit allocation,
memory, handle, and value premises. Reads agree with the retained objects and
their decoded source representations. Export lookup compares exact raw bytes.

These contracts describe ordinary Rust errors as well as success. Mutable
memory write-back requires the original byte length. Native identity issuance
and platform implementations remain subject to the obligations described in
[Runtime/Contracts](../Runtime/Contracts.lean).
-/

open Aeneas Aeneas.Std SpecExt

namespace Itasca.Runtime
open Integration Interp Store

/-- An empty store has executable certificates for every code interpretation.
The native wrapper supplies the positive identity: its counter starts at one
and advances with checked addition. That wrapper is outside extraction. -/
theorem runtime.store.Store.with_identity.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (id : Usize) (limits : runtime.store.StoreLimits)
    (positive : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits ⦃ store =>
      ExecutableInv view code store ∧ store.id = id ∧ store.limits = limits ∧
        Store.decodeStore view code store = ⟨[], [], [], [], [], []⟩ ⦄ :=
  _root_.Itasca.runtime.store.Store.with_identity.spec memory view code id limits positive

/-- Defining an external identity preserves executable metadata and the decoded
source store. Failure leaves the store unchanged; success appends one owned identity. -/
theorem runtime.store.Store.define_extern_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (identity : U64) :
    runtime.store.Store.define_extern_with memory allocator store identity ⦃ (result, after) =>
      ExecutableInv view code after ∧ Interp.FrameStoreMetadata store after ∧
      after.limits = store.limits ∧ decodeStore view code after = decodeStore view code store ∧
      match result with
      | .Err _ => after = store
      | .Ok address =>
        address.store = store.id ∧ address.index.val = store.externs.length ∧
        ValueInStore after (.ExternRef (some address)) ∧
        ∃ externs : alloc.vec.Vec U64, externs.val = store.externs.val ++ [identity] ∧
          after = {store with externs} ⦄ :=
  _root_.Itasca.runtime.store.Store.define_extern_with.spec memory allocator law view code store held identity

/-- A host definition either leaves the store unchanged or appends an issued
host with its exact structural signature, preserving executable certificates. -/
theorem runtime.store.Store.define_host_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.FuncType) (host : U64) :
    runtime.store.Store.define_host_with memory allocator store ty host ⦃ (result, after) =>
      ExecutableInv view code after ∧ StagedPrefix store after ∧
      Extend_store (decodeStore view code store) (decodeStore view code after) ∧
      match result with
      | .Err _ => after = store
      | .Ok address => address.store = store.id ∧ address.index.val = store.funcs.length ∧
        ExternalIssued after (.Func address) ∧ ValueInStore after (.FuncRef (some address)) ∧
        SpecExt.HostFunction (decodeStore view code after) address.index.val host.val
          (ty.params.val.map Interp.sourceType) (ty.results.val.map Interp.sourceType) ⦄ :=
  _root_.Itasca.runtime.store.Store.define_host_with.spec memory allocator law view code store held ty host

/-- Defining memory retains the supplied buffer bytes, establishes the declared
page bounds, and preserves the executable store. Every failure is atomic. -/
theorem runtime.store.Store.define_memory_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.MemType) (buffer : M) :
    runtime.store.Store.define_memory_with memory allocator store ty buffer ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok address => address.store = store.id ∧ address.index.val = store.memories.length ∧
        ExternalIssued after (.Memory address) ∧
        after.memories.val = store.memories.val ++ [{buf := buffer, maximum := ty.limits.max}] ∧
        (view buffer).length = ty.limits.min.val * 65536 ⦄ :=
  _root_.Itasca.runtime.store.Store.define_memory_with.spec memory allocator law view laws code store held ty buffer

/-- Defining a table appends exactly the declared number of null references;
all rejection and allocation failures leave the original store unchanged. -/
theorem runtime.store.Store.define_table_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.TableType) :
    runtime.store.Store.define_table_with memory allocator store ty ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok address => address.store = store.id ∧ address.index.val = store.tables.length ∧
        ExternalIssued after (.Table address) ∧
        ∃ elements : alloc.vec.Vec U64, elements.val = List.replicate ty.limits.min.val 0#u64 ∧
          after.tables.val = store.tables.val ++ [{elements, ty := ty.elem, maximum := ty.limits.max}] ⦄ :=
  _root_.Itasca.runtime.store.Store.define_table_with.spec memory allocator law view code store held ty

/-- A global definition accepts only an owned value of its declared type.
Success appends the exact decoded value; every rejection preserves the store. -/
theorem runtime.store.Store.define_global_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.wasm_types.GlobalType) (value : runtime.Value) (issued : IssuedValue store value) :
    runtime.store.Store.define_global_with memory allocator store ty value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok address => address.store = store.id ∧ address.index.val = store.globals.length ∧
        ExternalIssued after (.Global address) ∧ ty.valtype = Interp.rawType value ∧
        (decodeStore view code after).GLOBALS = (decodeStore view code store).GLOBALS ++
          [⟨.mk_globaltype (decodeMut ty.mutability) (Interp.sourceType ty.valtype),
            Interp.sourceValue value⟩] ⦄ :=
  _root_.Itasca.runtime.store.Store.define_global_with.spec memory allocator law view code store held ty value issued

/-- Setting an issued mutable global writes the requested address and exact
source value. Foreign, immutable, and mistyped writes leave the store unchanged. -/
theorem runtime.store.Store.set_global.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.GlobalAddr) (value : runtime.Value)
    (issued : ExternalIssued store (.Global address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.set_global memory store address value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok () => GlobalMutation store after (sourceValue value) ∧
        ∃ old : runtime.store.GlobalInst, store.globals.val[address.index.val]? = some old ∧
          old.ty.mutability = .Var ∧ old.ty.valtype = rawType value ∧
          (decodeStore view code after).GLOBALS = (decodeStore view code store).GLOBALS.set address.index.val
            ⟨.mk_globaltype (decodeMut old.ty.mutability) (sourceType old.ty.valtype), sourceValue value⟩ ⦄ :=
  _root_.Itasca.runtime.store.Store.set_global.spec memory view code store held address value issued valueIssued

/-- Setting a table updates exactly the issued table and requested element.
All ownership, type, and bounds rejections leave the store unchanged. -/
theorem runtime.store.Store.set_table.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (index : U32) (value : runtime.Value)
    (issued : ExternalIssued store (.Table address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.set_table memory store address index value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok () => ∃ old : runtime.store.TableInst, ∃ words : U64 × U64,
        store.tables.val[address.index.val]? = some old ∧ index.val < old.elements.length ∧
        elementValueType old.ty = rawType value ∧ runtime.value.encode value = .ok words ∧
        TableMutation store after address old words.1 ∧
        after = {store with
          tables := store.tables.set address.index {old with elements := old.elements.set (UScalar.cast .Usize index) words.1}} ⦄ :=
  _root_.Itasca.runtime.store.Store.set_table.spec memory view code store held address index value issued valueIssued

/-- A mutable memory borrow preserves executable certificates when the caller
writes back the same number of bytes. An error reply restores the original
visible bytes through the platform closure, without equating opaque buffers. -/
theorem runtime.store.Store.memory_mut.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.MemoryAddr) (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.memory_mut memory store address ⦃ (result, back) =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id ∧
        ∀ reply, ExecutableInv view code (back reply) ∧
          CumulativeStoreMutation view code store (back reply) ∧ back reply = store
      | .Ok bytes => ∃ object : runtime.store.MemInst M,
        address.store = store.id ∧ store.memories.val[address.index.val]? = some object ∧
        bytes = view object.buf ∧
        (∀ replacement : Slice U8, replacement.length = bytes.length →
          ExecutableInv view code (back (.Ok replacement)) ∧
          MemoryMutation view store (back (.Ok replacement)) address object ∧
          CumulativeStoreMutation view code store (back (.Ok replacement)) ∧
          (decodeStore view code (back (.Ok replacement))).MEMS =
            (decodeStore view code store).MEMS.set address.index.val
              ⟨(decodeMemory view object).TYPE, decodeBytes replacement.val⟩) ∧
        ∀ error, ExecutableInv view code (back (.Err error)) ∧
          CumulativeStoreMutation view code store (back (.Err error)) ⦄ :=
  _root_.Itasca.runtime.store.Store.memory_mut.spec memory view laws code store held address issued

/-- Memory growth preserves executable stores, including the failure sentinel. -/
theorem runtime.store.Store.grow_memory_with.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.MemoryAddr) (delta : U32)
    (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.grow_memory_with memory store address delta ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id ∧ after = store
      | .Ok pages => address.store = store.id ∧
          MemoryGrowth view code store address.index delta (pages, after) ⦄ :=
  _root_.Itasca.runtime.store.Store.grow_memory_with.spec memory view laws code store held address delta issued

/-- Table growth checks ownership and reference type before extending the table. -/
theorem runtime.store.Store.grow_table_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (delta : U32) (value : runtime.Value)
    (issued : ExternalIssued store (.Table address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.grow_table_with memory allocator store address delta value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err error => after = store ∧ (error = .WrongStore ∨ error = .BadArguments)
      | .Ok size => address.store = store.id ∧ ∃ words : U64 × U64,
          runtime.value.encode value = .ok words ∧
          TableGrowth store address.index delta words.1 (size, after) ⦄ :=
  _root_.Itasca.runtime.store.Store.grow_table_with.spec memory allocator law view code store held address delta value issued valueIssued

/-- Global reads return the value in the decoded global component. -/
theorem runtime.store.Store.global.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.GlobalAddr) (issued : ExternalIssued store (.Global address)) :
    runtime.store.Store.global memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok value => address.store = store.id ∧ ∃ object,
        store.globals.val[address.index.val]? = some object ∧
        (decodeStore view code store).GLOBALS[address.index.val]? = some (decodeGlobal object) ∧
        ValueInStore store value ∧ rawType value = object.ty.valtype ∧ sourceValue value = (decodeGlobal object).VALUE ⦄ :=
  _root_.Itasca.runtime.store.Store.global.spec memory view code store held address issued

/-- A memory read exposes the platform view of the decoded memory bytes. -/
theorem runtime.store.Store.memory.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.MemoryAddr)
    (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.memory memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok bytes => address.store = store.id ∧ ∃ object,
        store.memories.val[address.index.val]? = some object ∧ bytes = view object.buf ∧
        (decodeStore view code store).MEMS[address.index.val]? = some (decodeMemory view object) ∧
        (decodeMemory view object).BYTES = decodeBytes bytes.val ⦄ :=
  _root_.Itasca.runtime.store.Store.memory.spec memory view laws code store address issued

/-- Table size is the length of the decoded reference vector. -/
theorem runtime.store.Store.table_size.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (issued : ExternalIssued store (.Table address)) :
    runtime.store.Store.table_size memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok size => address.store = store.id ∧ ∃ object,
        store.tables.val[address.index.val]? = some object ∧ size.val = object.elements.length ∧
        (decodeStore view code store).TABLES[address.index.val]? = some (decodeTable object) ∧
        size.val = (decodeTable object).REFS.length ⦄ :=
  _root_.Itasca.runtime.store.Store.table_size.spec memory view code store held address issued

/-- Table reads expose exactly the selected decoded reference, or report the
checked element bound separately from a foreign table handle. -/
theorem runtime.store.Store.table_get.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (index : U32) (issued : ExternalIssued store (.Table address)) :
    runtime.store.Store.table_get memory store address index ⦃ result =>
      match result with
      | .Err error => (error = .WrongStore ∧ address.store ≠ store.id) ∨
        (error = .Trap .TableOutOfBounds ∧ address.store = store.id ∧ ∃ object,
          store.tables.val[address.index.val]? = some object ∧ object.elements.length ≤ index.val)
      | .Ok value => address.store = store.id ∧ ∃ object word,
        store.tables.val[address.index.val]? = some object ∧ object.elements.val[index.val]? = some word ∧
        (decodeStore view code store).TABLES[address.index.val]? = some (decodeTable object) ∧
        (decodeTable object).REFS[index.val]? = some (decodeRef object.ty word) ∧
        ValueInStore store value ∧ sourceValue value = refVal (decodeRef object.ty word) ⦄ :=
  _root_.Itasca.runtime.store.Store.table_get.spec memory view code store held address index issued

/-- Function type lookup returns the decoded type of the issued function. -/
theorem runtime.store.Store.func_type.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.FuncAddr) (issued : ExternalIssued store (.Func address)) :
    runtime.store.Store.func_type memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok signature => address.store = store.id ∧ ∃ function,
        store.funcs.val[address.index.val]? = some function ∧
        store.types.val[function.signature.val]? = some signature ∧
        (decodeStore view code store).FUNCS[address.index.val]? = some (decodeFunction code store function) ∧
        (decodeFunction code store function).TYPE = decodeFuncType signature ⦄ :=
  _root_.Itasca.runtime.store.Store.func_type.spec memory view code store held address issued

/-- External identities are the exact values retained at the issued address. -/
theorem runtime.store.Store.extern_identity.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (address : runtime.ExternAddr) (issued : IssuedValue store (.ExternRef (some address))) :
    runtime.store.Store.extern_identity memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok identity => address.store = store.id ∧ store.externs.val[address.index.val]? = some identity ⦄ :=
  _root_.Itasca.runtime.store.Store.extern_identity.spec memory store address issued

/-- Export lookup uses the first exact byte-name match. Returned handles are
issued and agree with the decoded instance exports, even for arbitrary queries. -/
theorem runtime.store.Store.export.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.InstanceAddr) (query : Slice U8)
    (issued : address.store = store.id → address.index.val < store.instances.length) :
    runtime.store.Store.export memory store address query ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok found => address.store = store.id ∧ ∃ inst,
        store.instances.val[address.index.val]? = some inst ∧
        found = exportSearch inst query 0 none ∧
        (found = none ↔ ∀ entry ∈ inst.module.module.env.exports.val, entry.name.val ≠ query.val) ∧
        ∀ external, found = some external → ExternalIssued store external ∧
          ∃ entry ∈ (decodeInstance store inst).EXPORTS,
            entry.NAME = decodeName query.val ∧ entry.ADDR = decodeExternal external ⦄ :=
  _root_.Itasca.runtime.store.Store.export.spec memory view code store held address query issued

end Itasca.Runtime
