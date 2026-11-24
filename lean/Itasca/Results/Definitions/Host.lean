import Itasca.Results.Definitions.Store.State
import Itasca.Results.Definitions.SourceMachine

/-!
# Host callbacks and observations

Read the observed callback exchange first, then HostReturn and HostLaws.
Callback errors retain the same store obligations as success. Divergence is
permitted and described separately for invocation termination.
-/

/-! ## Callback observations and source events

The callback boundary identifies an embedding host, whereas source execution
identifies a Wasm function address. The relation below checks that the source
address denotes the observed host and that the arguments and checked reply
agree. It intentionally permits aliases of the same host identity.
-/
namespace Itasca.Interp
open Aeneas Aeneas.Std Itasca.Representation

/-- Reference ownership checked at the API boundary. Issuance and address
bounds are separate store-invariant obligations. -/
def OwnedBy (id : Usize) : runtime.Value → Prop
  | .FuncRef (some address) => address.store = id
  | .ExternRef (some address) => address.store = id
  | _ => True

def ArgumentMatches (id : Usize) (value : runtime.Value) (ty : Itasca.wasm_types.ValueType) : Prop :=
  OwnedBy id value ∧ rawType value = ty

end Itasca.Interp

namespace Itasca.Platform
open Aeneas Aeneas.Std SpecExt Itasca.Representation

/-- A successful callback reply must match the callee's result signature and
belong to the returned store. Callback success alone does not establish this:
wrong arity, wrong value tags and foreign references become host traps. -/
def HostObservation.Accepted {M : Type} (observed : HostObservation M) (address : Nat) : Prop :=
  ∃ function signature, observed.after.funcs.val[address]? = some function ∧
    observed.after.types.val[function.signature.val]? = some signature ∧
    List.Forall₂ (Interp.ArgumentMatches observed.after.id) observed.returned.val signature.results.val

/-- One actual callback exchange accounts for one source host event. The
function address comes from source execution; metadata relates it to the actual
host identity. Both explicit host errors and invalid successful replies have
no source return values. No dispatch, scratch-buffer or loop witness appears. -/
def HostObservation.Matches {M : Type} (observed : HostObservation M) : HostEvent → Prop
  | .call address args reply =>
    (∃ function, observed.before.funcs.val[address]? = some function ∧
      function.code = .Host observed.identity) ∧
    args = observed.arguments.val.map sourceValue ∧
    match reply with
    | some values => observed.result = .Ok () ∧ observed.Accepted address ∧
        values = observed.returned.val.map sourceValue
    | none => observed.result ≠ .Ok () ∨ ¬observed.Accepted address

end Itasca.Platform


section HostContracts

/-!
## Host callback laws

`HostLaws` quantifies over each callback once. `HostReturn` describes what a
returned callback preserves, including errors. Divergence is allowed; invocation
termination and resource completeness impose their own additional premises.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt

/-- Some callback diverges when called on `store`. -/
def HostDiverges {M P : Type} (hooks : runtime.platform.Platform P M) (store : runtime.store.Store M) : Prop :=
  ∃ platform host args results, hooks.call_host platform store host args results = .div

/-- Obligations for one returned host callback. The host may mutate object
contents and publish new objects, but it must preserve existing code meanings,
ownership metadata and a well-typed source store. These obligations apply to
both successful replies and host errors. -/
structure HostReturn {M : Type} (view : M → Slice U8)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (code : Representation.CodeInterpretation) (before after : runtime.store.Store M)
    (returned : Slice runtime.Value) (afterCode : Representation.CodeInterpretation) : Prop where
  /-- Previously published code keeps its meaning. -/
  codeAgrees : Store.CodeAgreesOn before code afterCode
  /-- The returned store supports the same runtime capabilities. -/
  invariant : Inv afterCode after
  /-- The source store changes only as allowed by SpecTec host-store extension. -/
  extension : Extend_store (Representation.decodeStore view code before)
    (Representation.decodeStore view afterCode after)
  /-- The extended source store remains well typed. -/
  typed : Store_ok (Representation.decodeStore view afterCode after)
  /-- Existing function, type and instance entries, and the store identity, survive. -/
  metadata : Store.MetadataExtended before after
  /-- Previously issued external references remain in range. -/
  externs : before.externs.length ≤ after.externs.length
  /-- Returned references are issued by the returned store. -/
  issued : ∀ value ∈ returned.val, Store.IssuedValue after value

/-- Every callback from a store satisfying `Inv` may diverge or return with
`HostReturn`. It cannot panic. Ordinary host errors still preserve the store
and ownership obligations; successful replies are separately checked for
arity, types and ownership by the interpreter. Termination and resource
availability are separate premises. -/
def HostLaws {M P : Type} (hooks : runtime.platform.Platform P M) (view : M → Slice U8)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store, Inv code store → ∀ platform host args results,
    hooks.call_host platform store host args results ⦃ (_, _, after, returned) =>
      ∃ afterCode, HostReturn view Inv code store after returned afterCode ⦄div

end Itasca.Integration

end HostContracts

section HostDivergence

/-!
## Reachable callback divergence

`HostCallDiverged` names source-reachable callbacks that diverge, as a distinct
alternative to an infinite source execution.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- A source run from `initial` reaches a configuration whose store decodes a runtime store on
which some callback diverges. -/
def HostCallDiverged {M P : Type} (hooks : runtime.platform.Platform P M) (view : M → Slice U8)
    (initial : config) : Prop :=
  ∃ events code store ambient instrs,
    StepsH initial events ⟨⟨Representation.decodeStore view code store,ambient⟩,instrs⟩ ∧ HostDiverges hooks store

end Itasca.Integration

end HostDivergence
