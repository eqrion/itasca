import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Store.Invariant.OwnedInitializerErrors
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.Simd.FrameStep
import Itasca.Runtime.Interp.Machine.Calls.CallStackEntry
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Invariant.Rollback
import Itasca.Runtime.Store.Invariant.ErrorPost
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Integration.Execution.Dispatch.SignatureWords
import Itasca.Runtime.Integration.Api.InvocationBoundary
import Itasca.Runtime.Interp.Relations.ArgumentRejectionKind
import Itasca.Runtime.Interp.Invocation.Recording

/-!
Sections, each formerly its own module: CertifiedApi, ExecutableInv, ExecutableCallEntry, InvocationCanonicalResources, InvocationEntryResources.
-/

/-! ## CertifiedApi -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

/-- Public API invariant. Export descriptors retain namespace bounds in
addition to the static execution certificate; no execution conclusion is a field. -/
structure CertifiedApiStore
 {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends CertifiedSupportedStore view code store where
  exportBounds : Store.ExportBounds store

abbrev CertifiedExecutableApiStore {M : Type} :=
  @CertifiedApiStore M

/-- The retained component, body, module-map and export certificates imply
full generated source store typing; it is not an invariant field. -/
theorem CertifiedApiStore.source_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view code store) :
    Store_ok (Store.decodeStore view code store) :=
  Store.decode_store_typed view code store certified.shape certified.storeSyntax
    certified.typed certified.segmentBounds certified.exportBounds

theorem CertifiedApiStore.update {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedApiStore view code before)
    (mutation : CumulativeStoreMutation view code before after) :
    CertifiedApiStore view code after :=
  ⟨certified.toCertifiedSupportedStore.update mutation,
    certified.exportBounds.instances_eq mutation.metadata.instances⟩

theorem CertifiedApiStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedApiStore view after store :=
  ⟨certified.toCertifiedSupportedStore.change_code agrees,certified.exportBounds⟩

theorem CertifiedApiStore.install_code {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view code store) (sources : List funccode) :
    CertifiedApiStore view (Store.installCode code store.instances.len.val sources) store :=
  certified.change_code (Store.install_code_agrees store code sources)

end Itasca.Runtime.Integration

end

/-! ## ExecutableInv -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

/-- Public execution invariant with the two reachable-store ledgers retained
explicitly. Host freedom is deliberately not a field. -/
structure ExecutableInv {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop
    extends CertifiedExecutableApiStore view code store where
  segmentAccounting : Store.SegmentAccounting store
  capacities : Store.FunctionCapacities code store

namespace ExecutableInv

theorem well_formed {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) :
    wf_store (Store.decodeStore view code store) :=
  Store.decode_store_wf view code store held.shape held.storeSyntax

/-- Every store satisfying the public invariant has the generated semantic
store typing, including host functions. -/
theorem source_typed {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) :
    Store_ok (Store.decodeStore view code store) :=
  held.toCertifiedApiStore.source_typed

theorem update {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} (held : ExecutableInv view code before)
    (mutation : CumulativeStoreMutation view code before after) : ExecutableInv view code after :=
  ⟨held.toCertifiedApiStore.update mutation,
    mutation.segmentCounts.accounting mutation.metadata.instances held.segmentAccounting,
    held.capacities.metadata mutation.metadata.functions mutation.metadata.instances mutation.metadata.types mutation.metadata.identity⟩

end ExecutableInv
end Itasca.Runtime.Integration

end

/-! ## ExecutableCallEntry -/

section

/-! Lookup evidence for an owned public function handle. This API-layer evidence
is shared by correspondence, typing and divergence; representation foundations
remain independent of public invocation setup. -/
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

/-- The function and signature selected by one public function handle. -/
structure ExecutableCallEntry {M : Type} (store : runtime.store.Store M)
    (address : runtime.FuncAddr) where
  function : runtime.store.FuncInst
  signature : Itasca.wasm_types.FuncType
  functionLookup : store.funcs.val[address.index.val]? = some function
  signatureLookup : store.types.val[function.signature.val]? = some signature
  signatureBound : function.signature.val < store.types.val.length

/-- Issuance and ownership justify both lookups before indexing. -/
def ExecutableInv.call_entry {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (valid : ExecutableInv view code store) (address : runtime.FuncAddr)
    (issued : Store.ExternalIssued store (.Func address)) (owner : address.store = store.id) :
    ExecutableCallEntry store address := by
  have bound : address.index.val < store.funcs.val.length := issued owner
  let function := store.funcs.val[address.index.val]
  have hf : store.funcs.val[address.index.val]? = some function := List.getElem?_eq_getElem bound
  have signatureBound : function.signature.val < store.types.val.length :=
    (valid.shape.functions function (List.mem_of_getElem? hf)).1
  exact ⟨function,store.types.val[function.signature.val],hf,List.getElem?_eq_getElem signatureBound,signatureBound⟩
end Itasca.Runtime.Integration

end

/-! ## InvocationCanonicalResources -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Allocator refusal sizes for the public argument/result buffers. -/
def SignatureAllocation {A : Type} (allocator : runtime.platform.Alloc A) (signature : functype) : Prop :=
  (∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val≤signatureWords signature ∧
    allocator.reserve slots n=.ok (false,slots)) ∨
  (∃ (results : alloc.vec.Vec runtime.Value) (n : Usize), n.val≤signature.2.1.length ∧
    allocator.reserve results n=.ok (false,results))

/-- Actual refusal witnesses use only source signature/frame requirements.
Signature buffers are explicit; this does not revise the planned T4 contract. -/
def CanonicalInvocationResourceCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (initial : config) (store : _root_.store)
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
end Itasca.Runtime.Integration

end

/-! ## InvocationEntryResources -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem InvocationResourceCause.canonical {M P A : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M}
    {signature : Itasca.wasm_types.FuncType} {results : alloc.vec.Vec runtime.Value}
    {error : runtime.ExecError} (initial : config) (sourceStore : _root_.store) (address : funcaddr)
    (cause : InvocationResourceCause allocator exec store signature results error) :
    CanonicalInvocationResourceCause allocator hooks initial sourceStore (Store.decodeFuncType signature) address
      store.limits.max_values.val store.limits.max_frames.val error := by
  rcases cause.kind with rfl | rfl
  · apply Or.inl
    simpa only [InvocationResourceCause,signatureWords,Store.decodeFuncType,typeSlots] using cause
  · apply Or.inl
    rcases cause with ⟨n,amount,refused⟩ | ⟨n,amount,refused⟩
    · exact Or.inl ⟨exec.slots,n,amount,refused⟩
    · exact Or.inr ⟨results,n,by simpa only [Store.decodeFuncType,List.length_map] using Nat.le_trans (Nat.le_of_eq amount) (Nat.sub_le _ _),refused⟩

theorem CallCause.invocation_canonical {M P A : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {prepared : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {signature : Itasca.wasm_types.FuncType} {error : runtime.ExecError}
    (view : M → Slice U8) (code : Store.CodeInterpretation) (initial : config)
    (capacities : Store.FunctionCapacities code store) (typed : CoreFunctionsTyped view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (hf : store.funcs.val[address.index.val]?=some function) (hw : function.code=.Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]?=some inst) (hc : inst.module.functions.val[functionIndex.val]?=some compiled)
    (empty : prepared.frames.val=[])
    (cause : CallCause allocator hooks prepared store platform 0#usize compiled error) :
    CanonicalInvocationResourceCause allocator hooks initial (Store.decodeStore view code store)
      (Store.decodeFuncType signature) address.index.val store.limits.max_values.val store.limits.max_frames.val error := by
  cases error with
  | Terminated => exact ⟨platform,cause⟩
  | Exhausted reason =>
    cases reason with
    | CallStack =>
      apply Or.inl
      change store.limits.max_frames.val≤prepared.frames.length at cause
      have zero : prepared.frames.length=0 := by simp only [alloc.vec.Vec.length,empty,List.length_nil]
      have limit : store.limits.max_frames.val=0 := by omega
      simp [limit]
    | Values =>
      obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities typed
        address function instanceIndex functionIndex inst compiled hf hw hi hc
      change store.limits.max_values.val<(0#usize).val+compiled.slot_count.val at cause
      exact Or.inr (Or.inl ⟨words,capacity,by scalar_tac⟩)
    | Allocation =>
      obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities typed
        address function instanceIndex functionIndex inst compiled hf hw hi hc
      apply Or.inr; apply Or.inl; refine ⟨words,capacity,?_⟩
      rcases CallCause.source_allocation bound cause with ⟨n,amount,refused⟩ | refused
      · exact Or.inl ⟨prepared.slots,n,by simpa using amount,refused⟩
      · exact Or.inr ⟨prepared.frames,refused⟩
    | Objects => exact cause
  | _ => trivial
end Itasca.Runtime.Integration

end
