import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Store.Definitions
import Itasca.Results.Definitions.Runtime
import Itasca.Runtime.Interp.Definitions

open WebAssembly


/-! Internal projections of the unified host callback contract. These adapters
retain the proof-facing split between source semantics and concrete ownership. -/

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly

/-- The callback contract carries its current ghost interpretation explicitly. A call may
diverge; when it returns, its interpretation agrees on previously issued keys and fresh keys are
chosen by publication. Raw metadata retention remains a separate hypothesis. -/
def HostWorldSound {M P : Type} (hooks : runtime.platform.Platform P M)
    (view : M → Slice U8) (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store, Inv code store → ∀ platform host args results,
    hooks.call_host platform store host args results ⦃ (_, _, after, _) => ∃ afterCode,
      Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
      Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
        Store_ok (Representation.decodeStore view afterCode after) ⦄div

/-- Raw retention by every call of `host` from `store`. These laws do not follow from decoded
source-store extension. -/
structure HostRetention {M P : Type} (hooks : runtime.platform.Platform P M)
    (store : runtime.store.Store M) (host : U64) : Prop where
  /-- Returning calls retain the concrete metadata needed by suspended frames. -/
  framePrefix : ∀ p args results result nextPlatform after returned,
    hooks.call_host p store host args results = .ok (result, nextPlatform, after, returned) → Store.MetadataExtended store after
  /-- Returning calls do not shrink the number of issued extern identities. -/
  externs : ∀ p args results result nextPlatform after returned,
    hooks.call_host p store host args results = .ok (result, nextPlatform, after, returned) → store.externs.length ≤ after.externs.length
  /-- Every value returned to the caller is issued by the final store. -/
  issued : ∀ p args results result nextPlatform after returned,
    hooks.call_host p store host args results = .ok (result, nextPlatform, after, returned) →
      ∀ value ∈ returned.val, Store.IssuedValue after value

/-- Recover the source-world law from the single callback postcondition. -/
theorem HostLaws.sound {M P : Type} {hooks : runtime.platform.Platform P M}
    {view : M → Slice U8} {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop}
    (laws : HostLaws hooks view Inv) : HostWorldSound hooks view Inv := by
  intro code store held platform host args results
  apply WP.dspec_mono (laws code store held platform host args results)
  rintro ⟨status, next, after, returned⟩ ⟨afterCode, post⟩
  exact ⟨afterCode, post.codeAgrees, post.invariant, post.extension, post.typed⟩

/-- Recover retention for each actual returning call. -/
theorem HostLaws.retains {M P : Type} {hooks : runtime.platform.Platform P M}
    {view : M → Slice U8} {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop}
    (laws : HostLaws hooks view Inv) (code) (store) (held : Inv code store) (host) :
    HostRetention hooks store host := by
  have retained : ∀ p args results result nextPlatform after returned,
      hooks.call_host p store host args results = .ok (result, nextPlatform, after, returned) →
      Store.MetadataExtended store after ∧ store.externs.length ≤ after.externs.length ∧
        ∀ value ∈ returned.val, Store.IssuedValue after value := by
    intro p args results result nextPlatform after returned called
    have checked := laws code store held p host args results
    rw [called, WP.dspec_ok] at checked
    obtain ⟨_, post⟩ := checked
    exact ⟨post.metadata, post.externs, post.issued⟩
  exact ⟨fun p a r s n t v h => (retained p a r s n t v h).1,
    fun p a r s n t v h => (retained p a r s n t v h).2.1,
    fun p a r s n t v h => (retained p a r s n t v h).2.2⟩

/-- The former separate laws suffice for the unified contract as well. -/
theorem HostLaws.of_parts {M P : Type} {hooks : runtime.platform.Platform P M}
    {view : M → Slice U8} {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop}
    (sound : HostWorldSound hooks view Inv)
    (retains : ∀ code store, Inv code store → ∀ host, HostRetention hooks store host) :
    HostLaws hooks view Inv := by
  intro code store held platform host args results
  have checked := sound code store held platform host args results
  generalize called : hooks.call_host platform store host args results = call at checked ⊢
  cases checked with
  | div => exact .div _
  | @ret _ answer post =>
    rcases answer with ⟨result, nextPlatform, after, returned⟩
    obtain ⟨afterCode, agrees, valid, extension, typed⟩ := post
    have kept := retains code store held host
    exact .ret ⟨afterCode, agrees, valid, extension, typed,
      kept.framePrefix _ _ _ _ _ _ _ called, kept.externs _ _ _ _ _ _ _ called,
      kept.issued _ _ _ _ _ _ _ called⟩

end Itasca.Integration

/-! ## Integration / Invocation / Outcomes -/

section IntegrationInvocationOutcomes

/-!
### Recorded invocation outcomes

Source error outcomes, initial-host resource causes and API rejection distinguish
unchanged entry failures from execution with committed effects. Returned outcomes
retain the final code interpretation, store certificate and actual host-event log.
-/

/-!
## Event-bearing invocation errors

`EventfulInvocationError` records the classified concrete/source cause of an invocation
error with its event history.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std WebAssembly

/-- Source outcomes for errors after checked invocation entry. Resource and
interrupt cases retain the exact reached store, including callback effects;
local cause theorems separately constrain why those errors were chosen. -/
def EventfulInvocationError (initial : config) (events : List HostEvent)
    (store : WebAssembly.store) (ambient : frame) : runtime.ExecError → Prop
  | .Trap _ => StepsH initial events ⟨⟨store,ambient⟩,[.TRAP]⟩
  | .Exhausted _ | .Terminated => ∃ body, StepsH initial events ⟨⟨store,ambient⟩,body⟩
  | _ => False

end Itasca.Integration

end IntegrationInvocationOutcomes

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Representation

/-- API rejection is confined to ownership/type errors on invalid inputs.
An owned function with owned, source-typed arguments cannot be rejected. The
actual checker and its private traversal are not needed to state this condition. -/
def InvocationInputError {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (error : runtime.ExecError) : Prop :=
  (error = .WrongStore ∨ error = .BadArguments) ∧
  ¬ (address.store = store.id ∧ (∀ value ∈ args.val, Store.ValueInStore store value) ∧
    InvocationArgumentsTyped (decodeStore view code store) address.index.val (args.val.map sourceValue))

end Itasca.Integration

section IntegrationInvocationBoundaryCauses

/-!
### Invocation boundary causes

`InvocationBoundaryCause` classifies the source/host boundary conditions responsible for
an actual invocation error.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std WebAssembly

/-- Call-stack exhaustion is bounded by decoded frame nesting; termination
retains a concrete interrupt decision. -/
def InvocationBoundaryCause {M P : Type} (hooks : runtime.platform.Platform P M)
    (initial : config) (maxFrames : Nat) : runtime.ExecError → Prop
  | .Exhausted .CallStack => maxFrames ≤ Spec.frameDepth initial ∨
      ∃ final, StepsH initial [] final ∧ maxFrames ≤ Spec.frameDepth final
  | .Terminated => ∃ before after, hooks.interrupt before = .ok (.Terminate, after)
  | _ => True

end Itasca.Integration

end IntegrationInvocationBoundaryCauses

section IntegrationInvocationSignatureResources

/-!
### Invocation signature resources

Decoded parameter/result widths determine public buffer demand. Host allocation
witnesses retain actual refused requests bounded by that same signature, including
the shared slot region and argument/result vectors.
-/

/-!
## Physical signature width

`signatureWords` computes the concrete word demand of a source function signature.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std WebAssembly

/-- Public buffer storage is computed from decoded parameter/result types. -/
def signatureWords : functype → Nat
  | .mk_functype (.mk_list params) (.mk_list results) => max (Representation.slots params) (Representation.slots results)

end Itasca.Integration

/-!
## Host signature allocation

Reached host-call allocation witnesses are bounded by the selected source signature and
its argument/result storage requirements.
-/

namespace Itasca.Integration
open Itasca.Representation

open Aeneas Aeneas.Std WebAssembly

/-- Bounded actual requests for a host's shared slot region and argument/result
vectors. The signature buffer demand remains explicit. -/
def HostSignatureAllocation {A : Type} (allocator : runtime.platform.Alloc A)
    (params results : List valtype) (base : Nat) : Prop :=
  (∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val≤base+max (Representation.slots params) (Representation.slots results) ∧
    allocator.reserve slots n=.ok (false,slots)) ∨
  (∃ (arguments : alloc.vec.Vec runtime.Value) (n : Usize), n.val≤params.length ∧
    allocator.reserve arguments n=.ok (false,arguments)) ∨
  (∃ (returned : alloc.vec.Vec runtime.Value) (n : Usize), n.val≤results.length ∧
    allocator.reserve returned n=.ok (false,returned))

end Itasca.Integration

end IntegrationInvocationSignatureResources

section IntegrationExecutableStore

open Itasca.Representation

/-!
### Source invocation resources

Source signatures and conservative function-frame budgets explain value and
allocation errors without describing emitted function instructions.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- Allocator refusal sizes for the public argument/result buffers. -/
def SignatureAllocation {A : Type} (allocator : runtime.platform.Alloc A) (signature : functype) : Prop :=
  (∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val≤signatureWords signature ∧
    allocator.reserve slots n=.ok (false,slots)) ∨
  (∃ (results : alloc.vec.Vec runtime.Value) (n : Usize), n.val≤signature.2.1.length ∧
    allocator.reserve results n=.ok (false,results))

/-- Actual refusal witnesses use source signature/frame requirements, including
the concrete requests for signature buffers and reached invocation frames. -/
def CanonicalInvocationResourceCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (initial : config) (store : WebAssembly.store)
    (signature : functype) (address : funcaddr) (valueLimit frameLimit : Nat) : runtime.ExecError → Prop
  | .Exhausted .Values =>
    valueLimit<signatureWords signature ∨
    (∃ words, SourceCanonicalFunctionCapacity store address words ∧ valueLimit<words) ∨
    ∃ source callee base words, StepsH initial [] (SourceMachine.decode source) ∧
      SourceInvocationSite source callee base ∧ SourceCanonicalFunctionCapacity source.store callee words ∧
      valueLimit<base+words
  | .Exhausted .Allocation => SignatureAllocation allocator signature ∨
    (∃ words, SourceCanonicalFunctionCapacity store address words ∧
      ((∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val≤words ∧ allocator.reserve slots n=.ok (false,slots)) ∨
        ∃ frames : alloc.vec.Vec runtime.interp.Frame, allocator.reserve frames 1#usize=.ok (false,frames))) ∨
    ∃ source, StepsH initial [] (SourceMachine.decode source) ∧ SourceInvocationAllocation allocator source
  | .Exhausted .Objects => False
  | error => InvocationBoundaryCause hooks initial frameLimit error

end Itasca.Integration

end IntegrationExecutableStore

section IntegrationExecutionResourceCauses

/-!
### Source-side dispatch causes

`DispatchResourceCause` describes the source resource boundary that explains
a refusal, without requiring the execution proof's simulation certificate.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- A source-level explanation of a dispatch refusal. The reached store supplies
its current limits, since a host may have changed them. Allocation and host
refusals name the actual platform operations; no compiled frame, program
counter, simulation invariant or interpreter transition is part of this contract. -/
def DispatchResourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    (source : SourceMachine.AState) (store : runtime.store.Store M) (platform : P)
    (after : runtime.store.Store M) (nextPlatform : P) : runtime.ExecError → Prop
  | .Exhausted .Values => ∃ address base, SourceInvocationSite source address base ∧
      ((∃ words,SourceCanonicalFunctionCapacity source.store address words ∧
        store.limits.max_values.val<base+words) ∨
       ∃ identity params results,HostFunction source.store address identity params results ∧
        store.limits.max_values.val<base+max (Representation.slots params) (Representation.slots results))
  | .Exhausted .Allocation => SourceInvocationAllocation allocator source ∨
      ∃ address identity base params results,SourceInvocationSite source address base ∧
        HostFunction source.store address identity params results ∧ HostSignatureAllocation allocator params results base
  | .Exhausted .CallStack => store.limits.max_frames.val≤Spec.frameDepth (SourceMachine.decode source) ∨
      ∃ identity p args defaults returned,
        hooks.call_host p store identity args defaults=.ok (.Err .StackOverflow,nextPlatform,after,returned)
  | .Terminated => ∃ after,hooks.interrupt platform=.ok (.Terminate,after)
  | .Exhausted .Objects => False
  | _ => True

end Itasca.Integration

end IntegrationExecutionResourceCauses

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Representation Itasca.Interp Itasca.Store Itasca.Spec

/-- Explicitly rule out callback-reported stack exhaustion. Normal host traps
and invalid dynamically checked results remain source trap outcomes. -/
def NoHostStackOverflow {M P : Type} (hooks : runtime.platform.Platform P M)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store,Inv code store → ∀ p identity args defaults nextPlatform after returned,
    hooks.call_host p store identity args defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned)


/-- The generated instantiation configuration at the actual publication
cutpoint: source element/data initialization followed by the optional start. -/
def sourceInstantiationConfiguration {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : Binary.Module) : config :=
  ⟨⟨decodeStore view code store, ⟨[], decodeInstance store inst⟩⟩,
    (Spec.Segment.elementPrograms (raw.elements.map Module.Elaboration.element)).flatten.map admininstr_instr ++
    ((Spec.Segment.dataPrograms (raw.data.map Module.Data.translate)).flatten.map admininstr_instr ++
      (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩


def InitialHostSourceResourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    (store after : runtime.store.Store M) (identity : U64) (signature : Itasca.wasm_types.FuncType) : runtime.ExecError → Prop
  | .Exhausted .Values => store.limits.max_values.val<signatureWords (Itasca.Translation.Environment.funcType signature)
  | .Exhausted .Allocation => HostSignatureAllocation allocator (signature.params.val.map Itasca.Translation.valueType) (signature.results.val.map Itasca.Translation.valueType) 0
  | .Exhausted .CallStack => ∃ p args defaults host returned,
      hooks.call_host p store identity args defaults=.ok (.Err .StackOverflow,host,after,returned)
  | .Terminated => ∃ before after,hooks.interrupt before=.ok (.Terminate,after)
  | .Exhausted .Objects => False
  | _ => True


/-- Source storage demand at a selected point, including defined and host
callees and suspended callers. No native success or trace appears here. -/
structure SourceWorldResources (valueLimit frameLimit : Nat) (source : SourceMachine.AState) : Prop where
  frames : frameDepth (SourceMachine.decode source)<frameLimit
  defined : ∀ address base words,SourceInvocationSite source address base →
    SourceCanonicalFunctionCapacity source.store address words → base+words≤valueLimit
  host : ∀ address identity base params results,SourceInvocationSite source address base →
    HostFunction source.store address identity params results → base+max (Representation.slots params) (Representation.slots results)≤valueLimit


/-- Every source run of an invocation fits the given value and frame limits: the callee
signature and frame, the frame depth of every reachable configuration, and every function
called from a reachable state. Host replies are arbitrary typed values, so this quantifies
over all host behaviors. -/
structure SourceResourcesFit (store : WebAssembly.store) (address : funcaddr) (initial : config)
    (valueLimit frameLimit : Nat) : Prop where
  signature : ∀ function,store.FUNCS[address]?=some function → signatureWords function.TYPE≤valueLimit
  entry : ∀ words,SourceCanonicalFunctionCapacity store address words → words≤valueLimit
  frames : ∀ events final,StepsH initial events final → frameDepth final<frameLimit
  reachable : ∀ events source,StepsH initial events (SourceMachine.decode source) →
    SourceWorldResources valueLimit frameLimit source


end Itasca.Integration

section IntegrationInvocationResources

/-!
### Invocation resource causes

Defined-function causes explain refusal at the original call boundary or an
actual reached dispatch in the current code world. The public invocation cause
joins those witnesses with initial-host causes and unchanged API rejections.
-/

/-!
## Defined-function resource causes

`WorldDefinedSourceResourceCause` retains source demand and concrete resource causes for
defined-function execution in an evolving code world.
-/

namespace Itasca.Integration
open Itasca.Representation

open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- A failure is explained at the original call boundary or at a reachable
source configuration in the evolving store. The retained invariant and decoding
identify the reached store, including limits changed by host callbacks. Internal
proofs construct this witness from the actual recorded execution; their machine
simulation certificates are not premises of the public resource explanation. -/
def WorldDefinedSourceResourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  let initial := ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
  CanonicalInvocationResourceCause allocator hooks initial (Representation.decodeStore view code store)
    (Itasca.Translation.Environment.funcType signature) address.index.val store.limits.max_values.val store.limits.max_frames.val error ∨
  ∃ source reachedCode reachedStore reachedPlatform nextPlatform events,
    StepsH initial events (SourceMachine.decode source) ∧
    source.store = Representation.decodeStore view reachedCode reachedStore ∧
    Inv reachedCode reachedStore ∧
    DispatchResourceCause hooks allocator source reachedStore reachedPlatform after nextPlatform error

end Itasca.Integration

/-!
## Joined invocation resource causes

`ExecutableWorldInvocationSourceCause` connects concrete invocation resource errors to
their classified source-side causes.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- Resource and boundary errors retain the original public selection or the
actual reached code world, including functions published by earlier callbacks. -/
def ExecutableWorldInvocationSourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (code : Representation.CodeInterpretation) (store : runtime.store.Store M) (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  ((error=.BadArguments ∨ error=.WrongStore) ∧ after=store) ∨
  ∃ function signature,store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature ∧
    ((∃ ii fi,function.code=.Wasm ii fi ∧
      WorldDefinedSourceResourceCause
        hooks allocator view code Inv store Spec.invocationFrame address signature args after error) ∨
     ∃ identity,function.code=.Host identity ∧ InitialHostSourceResourceCause hooks allocator store after identity signature error)

end Itasca.Integration

end IntegrationInvocationResources

/-! Private executable-store invariant and its simulation outcomes. The public protocol quantifies an abstract store predicate instead of exposing these certificates. -/

section IntegrationStoreCertificate

/-!
### Certified supported stores

`CertifiedSupportedStore` combines retained source/code shape and support certificates
below the public API invariant.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std

/-- Common static store certificate indexed by source syntax and concrete
function emission. Execution semantics remain separate checked theorems. -/
structure CertifiedSupportedStore
 {M : Type} (view : M → Slice U8)
    (code : Representation.CodeInterpretation) (store : runtime.store.Store M) : Prop where
  /-- Current object indices and decoded payloads satisfy the retained store shape. -/
  shape : Representation.Shape view store
  /-- Every interpreted instance supplies well-formed source syntax. -/
  storeSyntax : Store.StoreSyntax code store
  /-- Interpreted function bodies satisfy their source typing judgments. -/
  typed : Interp.CoreFunctionsTyped view code store
  /-- Decoded functions belong to the source instruction families modeled here. -/
  supported : SourceMachine.FunctionsSupported (Representation.decodeStore view code store)
  /-- Concrete functions carry their syntactic source/code correspondence. -/
  compiled : Interp.Machine.CompiledFunctions code store
  /-- Retained data/element lengths fit the binary count space. -/
  segmentBounds : Store.SegmentBounds store

end Itasca.Integration

end IntegrationStoreCertificate

namespace Itasca.Integration
open Aeneas Aeneas.Std
/-- Public API invariant. Export descriptors retain namespace bounds in
addition to the static execution certificate; no execution conclusion is a field. -/
structure CertifiedApiStore
 {M : Type} (view : M → Slice U8)
    (code : Representation.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends CertifiedSupportedStore view code store where
  /-- Retained exports have valid object indices and decoded names. -/
  exportBounds : Store.ExportBounds store

/-- Public execution invariant with the two reachable-store ledgers retained
explicitly. Host freedom is deliberately not a field. -/
structure ExecutableInv {M : Type} (view : M → Slice U8)
    (code : Representation.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends CertifiedApiStore view code store where
  /-- Retained data/element segments agree with their accounting ledgers. -/
  segmentAccounting : Store.SegmentAccounting store
  /-- Every interpreted function carries its source-frame capacity bounds. -/
  capacities : Representation.FunctionCapacities code store

end Itasca.Integration

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp Itasca.Representation
/-- The public entry checks that reject a call before any state changes: a handle from
another store, or arguments that fail the callee signature check. -/
def InvocationRejected {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (error : runtime.ExecError) : Prop :=
  (address.store≠store.id ∧ error=.WrongStore) ∨
  ∃ function signature,store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature ∧
    runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params)=.ok (.Err error)

/-- Public source correspondence at the exact concrete log, allowing callbacks
to publish new code while preserving existing issued instances. -/
def ExecutableWorldRecordedOutcome {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Representation.CodeInterpretation) (before : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (address : runtime.FuncAddr)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (result : core.result.Result Unit runtime.ExecError) (execution : runtime.interp.Execution)
    (after : runtime.store.Store M) (nextPlatform : P) (returned : alloc.vec.Vec runtime.Value)
    (events : List HostEvent) : Prop :=
  ∃ afterCode, Store.CodeAgreesOn before code afterCode ∧
  ExecutableInv view afterCode after ∧ Store.MetadataExtended before after ∧
  Extend_store (Representation.decodeStore view code before) (Representation.decodeStore view afterCode after) ∧
  (∃body,StepsH initial events ⟨⟨Representation.decodeStore view afterCode after,Spec.invocationFrame⟩,body⟩) ∧
  (result=.Ok () → (StepsH initial events
    ⟨⟨Representation.decodeStore view afterCode after,Spec.invocationFrame⟩,vals (returned.val.map sourceValue)⟩) ∧
    (∀value∈returned.val,Store.ValueInStore after value)) ∧
  (∀error,result=.Err error →
    (InvocationRejected memory before address args error ∧ (result,execution,after,nextPlatform,returned)=(.Err error,exec,before,platform,results) ∧ events=[]) ∨
    EventfulInvocationError initial events (Representation.decodeStore view afterCode after) Spec.invocationFrame error)

end Itasca.Integration

section IntegrationInvocationBehavior

/-!
### Public invocation behavior

`InvocationBehaves` relates the actual returned computation, recorded events and
retained store to source behavior, including the stated divergence alternatives.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std WebAssembly Itasca.Interp Itasca.Representation

/-- A returned result carries the exact event log of `recordedInvokeWith`, the source outcome for
that log and a resource cause for every error. Divergence is an infinite source run, or the source
reaches a store on which a callback diverges. -/
def InvocationBehaves {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (outcome : Result (core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value)) : Prop :=
  outcome ⦃ (result, execution, after, nextPlatform, returned) => ∃ events,
    recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok ((result, execution, after, nextPlatform, returned),events) ∧
    ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial result execution after nextPlatform returned events ∧
    ∀ error, result = .Err error → ExecutableWorldInvocationSourceCause hooks allocator view
      (ExecutableInv view) code store address args after error ⦄div ∧
  (outcome = .div → Spec.InfiniteSourceWithEvents initial ∨ HostCallDiverged hooks view initial)

end Itasca.Integration

end IntegrationInvocationBehavior

namespace Itasca.Integration
open Aeneas Aeneas.Std
/-- An internal dispatch witness, established from exact runtime mutation
footprints. Segment contents may change; their checked bounds remain explicit. -/
structure CumulativeStoreMutation {M : Type} (view : M → Slice U8)
    (code : Representation.CodeInterpretation) (before after : runtime.store.Store M) : Prop where
  metadata : Store.MetadataPreserved before after
  externs : after.externs = before.externs
  shape : Representation.Shape view after
  segmentBounds : Store.SegmentBounds after
  extension : Extend_store (Representation.decodeStore view code before) (Representation.decodeStore view code after)
  segmentCounts : Store.SegmentCounts before after
  limits : after.limits = before.limits

end Itasca.Integration

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Representation Itasca.Store
/-- Every resource error is a preparation refusal before publication or a segment setup refusal
after it. -/
def InstantiationResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (oldCode : CodeInterpretation)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (raw : Binary.Module)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  match error with
  | .Exhausted _ | .Terminated =>
    (after=before ∧ ∃ limit,error=.Exhausted limit ∧ ∃ staged,
      runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false=
        .ok (.Err error,staged,platform,false) ∧
      PrecommitResourceEvidence memory hooks floats allocator before module imports platform error) ∨
    ∃ ready inst,
      ready.instances.val[before.instances.len.val]?=some inst ∧ inst.module=module ∧
      fun_instantiate (decodeStore view oldCode before) (Module.Elaboration.moduleOf raw) (imports.val.map decodeExternal)
        (sourceInstantiationConfiguration view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready inst raw) ∧
      runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id,before.instances.len⟩ false=
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false ∧
      after=ready ∧ SegmentSetupCause allocator ready inst.module error
  | _ => True
end Itasca.Integration
