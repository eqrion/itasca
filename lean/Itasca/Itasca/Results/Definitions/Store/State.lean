import Aeneas
import ItascaRust.Types
import Itasca.Results.Definitions.Binary
import Itasca.Results.Definitions.Platform
import ItascaRust.Funs
import Itasca.Results.Definitions.Representation
import WebAssembly

/-!
# Store observations and effects

Issued handles and values, decoded reads and writes, source-store extension, and
code interpretation describe the observable store API. Prepublication rejection
is distinguished from traps after publication. Resource counters and allocation
strategies are internal and are not part of these effects.
-/

section StoreExternals

/-!
## Store handles, values and lookup

Issued and foreign identities, source decoding and exact export lookup describe the values crossing the store API boundary.
-/

/-!
## Issued and foreign handles

External-handle predicates connect opaque store identities and object indices to the
concrete store that issued them.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- A private external handle is either foreign or names an issued object.
Foreign handles remain admitted here because the API reports WrongStore. -/
def ExternalIssued {M : Type} (store : runtime.store.Store M) : runtime.Extern → Prop
  | .Func address => address.store = store.id → address.index.val < store.funcs.length
  | .Table address => address.store = store.id → address.index.val < store.tables.length
  | .Memory address => address.store = store.id → address.index.val < store.memories.length
  | .Global address => address.store = store.id → address.index.val < store.globals.length

end Itasca.Store

/-!
## Issued and foreign values

Value predicates distinguish references issued by the current concrete store from
foreign references at public API boundaries.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- A public value is either owned by this store or carries a foreign store
identity. Same-store references must denote an issued address. -/
def IssuedValue {M : Type} (s : runtime.store.Store M) (value : runtime.Value) : Prop :=
  match value with
  | .FuncRef (some address) => address.store = s.id → address.index.val < s.funcs.length
  | .ExternRef (some address) => address.store = s.id → address.index.val < s.externs.length
  | _ => True

end Itasca.Store

/-!
## External-handle decoding

`decodeExternal` interprets issued concrete externals as source objects for import
linking.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

def decodeExternal : runtime.Extern → externaddr
  | .Func address => .FUNC address.index.val
  | .Table address => .TABLE address.index.val
  | .Memory address => .MEM address.index.val
  | .Global address => .GLOBAL address.index.val

end Itasca.Store

/-!
## Decoded export lookup

Export matching relates exact byte names to source exports and owned handles.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- A returned external handle belongs to this store and names an existing
object. Input admissibility remains separate because foreign inputs are rejected. -/
def ExternalInStore {M : Type} (store : runtime.store.Store M) : runtime.Extern → Prop
  | .Func address => address.store = store.id ∧ address.index.val < store.funcs.length
  | .Table address => address.store = store.id ∧ address.index.val < store.tables.length
  | .Memory address => address.store = store.id ∧ address.index.val < store.memories.length
  | .Global address => address.store = store.id ∧ address.index.val < store.globals.length

/-- An export's exact byte name and decoded address match the query and handle.
Byte equality matters: decoding an arbitrary invalid UTF-8 query can lose bytes.
This relation describes the export map, with no search cursor or accumulator. -/
def ExportMatches (inst : runtime.store.ModuleInst) (query : Slice U8) (external : runtime.Extern) : Prop :=
  ∃ entry ∈ inst.module.module.env.exports.val, entry.name.val = query.val ∧
    Representation.decodeExport inst entry = ⟨Itasca.Binary.nameOfBytes query.val,decodeExternal external⟩

end Itasca.Store

end StoreExternals

section StoreCodeAgreement

open Itasca.Representation

/-!
## Code interpretation agreement

`CodeAgreesOn` relates interpretations on retained code; `installCode` publishes the new
module's source bodies at its instance index.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- New ghost code assignments agree on every already issued instance. This is
source syntax correspondence, not an execution theorem. -/
def CodeAgreesOn {M : Type} (store : runtime.store.Store M)
    (before after : CodeInterpretation) : Prop :=
  ∀ index inst, store.instances.val[index]? = some inst →
    ∀ function, after index inst.module function = before index inst.module function

/-- Install the source code for a fresh instance. Existing instance keys retain
their previous interpretation even when their compiled modules coincide. -/
def installCode (before : CodeInterpretation) (fresh : Nat) (source : List funccode) : CodeInterpretation :=
  fun index module function => if index = fresh then source.getD function default else before index module function

end Itasca.Store

end StoreCodeAgreement

section StoreMetadataPreservation

open Itasca.Representation

/-!
## Preserved metadata

Content mutation keeps the store identity and its function, type and instance
tables unchanged. These are public object identities, independent of frame layout.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- Content mutation preserves the store identity and its function, type and
instance tables. Object payloads and resource counters may change. -/
structure MetadataPreserved {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  functions : after.funcs = before.funcs
  types : after.types = before.types
  instances : after.instances = before.instances

end Itasca.Store

end StoreMetadataPreservation

section StoreMetadataExtension

/-!
## Extended metadata

Object creation may append function, type and instance entries. Existing entries
retain their exact identities and indices; object contents may still change.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- Object creation retains the store identity and every old function, type and
instance entry. New entries may be appended; object payloads may change. -/
structure MetadataExtended {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  functions : after.funcs.val.take before.funcs.length = before.funcs.val
  types : after.types.val.take before.types.length = before.types.val
  instances : after.instances.val.take before.instances.length = before.instances.val

end Itasca.Store

end StoreMetadataExtension

section StoreShape

open Itasca.Representation

/-!
## Retained store shape

Instance/store syntax, value membership and segment bounds describe the retained object
structure used to derive source store typing.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- API reference values name an existing object of this store. The additional
encoding bounds rule out the reserved null sentinel wrapping around. -/
def ValueInStore {M : Type} (s : runtime.store.Store M) (value : runtime.Value) : Prop :=
  Representation.ValueOwnedFits s.id value ∧ match value with
  | .FuncRef (some a) => a.index.val < s.funcs.length
  | .ExternRef (some a) => a.index.val < s.externs.length
  | _ => True

end Itasca.Store

end StoreShape

section StoreGrowth

open Itasca.Representation

/-!
## Memory and table growth effects

Growth relations describe retained prefixes, appended zero/initial values, returned old
sizes and the object counts of the resulting store.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- A successful memory growth is SpecTec growth at exactly one source address.
The failure sentinel preserves every source object. -/
def MemoryGrown (before after : _root_.store) (address delta returned : Nat) : Prop :=
  (returned = U32.max ∧ after = before) ∨
  ∃ old next, before.MEMS[address]? = some old ∧
    fun_growmemory old delta (some next) ∧ returned = old.BYTES.length / 65536 ∧
    after = {before with MEMS := before.MEMS.set address next}

/-- A successful table growth is SpecTec growth with the caller's source reference.
The failure sentinel preserves every source object. -/
def TableGrown (before after : _root_.store) (address delta returned : Nat) (value : val) : Prop :=
  (returned = U32.max ∧ after = before) ∨
  ∃ old next reference, before.TABLES[address]? = some old ∧ val_ref reference = value ∧
    fun_growtable old delta reference (some next) ∧ returned = old.REFS.length ∧
    after = {before with TABLES := before.TABLES.set address next}

end Itasca.Store

end StoreGrowth

/-! ## Source store updates -/

namespace Itasca.Store
open Aeneas Aeneas.Std WebAssembly

/-- Adding an object retains every existing source object, including mutable
contents. This is stronger than source type extension, which permits writes. -/
def SourceStorePrefix (before after : _root_.store) : Prop :=
  after.FUNCS.take before.FUNCS.length = before.FUNCS ∧
  after.GLOBALS.take before.GLOBALS.length = before.GLOBALS ∧
  after.TABLES.take before.TABLES.length = before.TABLES ∧
  after.MEMS.take before.MEMS.length = before.MEMS ∧
  after.ELEMS.take before.ELEMS.length = before.ELEMS ∧
  after.DATAS.take before.DATAS.length = before.DATAS

/-- A global write changes only the selected mutable source global. -/
def GlobalUpdate (before after : _root_.store) (address : Nat) (value : val) : Prop :=
  ∃ old, before.GLOBALS[address]? = some old ∧
    old.TYPE = .mk_globaltype (some .MUT) (Representation.valueType value) ∧
    after = {before with GLOBALS := before.GLOBALS.set address {old with VALUE := value}}

/-- A table write replaces one in-bounds source reference of the table's type.
Every other source object and the table's type and length are unchanged. -/
def TableUpdate (before after : _root_.store) (address index : Nat) (value : val) : Prop :=
  ∃ old reference, before.TABLES[address]? = some old ∧ index < old.REFS.length ∧
    val_ref reference = value ∧
    (match old.TYPE with | .mk_tabletype _ type => Representation.valueType value = valtype_reftype type) ∧
    after = {before with TABLES := before.TABLES.set address {old with REFS := old.REFS.set index reference}}

/-- A memory write replaces exactly the selected source byte sequence, retaining
its length, declared type, and every other source object. -/
def MemoryUpdate (before after : _root_.store) (address : Nat) (bytes : List byte) : Prop :=
  ∃ old, before.MEMS[address]? = some old ∧ bytes.length = old.BYTES.length ∧
    after = {before with MEMS := before.MEMS.set address {old with BYTES := bytes}}

end Itasca.Store

section StoreSegmentAccounting

/-!
## Segment accounting ledgers

Segment counts and accounting retain the data/element resources required by the
executable store invariant.
-/

namespace Itasca.Store

open Aeneas Aeneas.Std

/-- Instruction execution may drop segment payloads while retaining the number
of issued segment addresses. -/
structure SegmentCounts {M : Type} (before after : runtime.store.Store M) : Prop where
  elements : after.elems.length = before.elems.length
  datas : after.datas.length = before.datas.length

end Itasca.Store

end StoreSegmentAccounting

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Precommit rejections are linking, foreign-store handles, or embedding-resource
failures. Segment traps arise only after publication. -/
def PrecommitError : runtime.ExecError → Prop
  | .Link _ => True
  | .WrongStore => True
  | .Exhausted _ => True
  | _ => False

end Itasca.Store

section StoreMutationEffects

/-!
## Cumulative store mutation

`StoreMutation` retains identities, source extension, segment counts and limits.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std

/-- Observable preservation shared by store mutations. Object contents may
change, but issued identities, decoded source extension, segment counts and
configured limits remain available to callers. Private representation shape
is established inside the implementation proof. -/
structure StoreMutation {M : Type} (view : M → Slice U8)
    (code : Representation.CodeInterpretation) (before after : runtime.store.Store M) : Prop where
  metadata : Store.MetadataPreserved before after
  externs : after.externs = before.externs
  extension : Extend_store (Representation.decodeStore view code before) (Representation.decodeStore view code after)
  segmentCounts : Store.SegmentCounts before after
  limits : after.limits = before.limits

end Itasca.Integration

end StoreMutationEffects
