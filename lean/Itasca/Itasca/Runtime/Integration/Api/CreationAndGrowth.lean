import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Store.Invariant.CoreInstantiationSource
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.Simd.FrameStep
import Itasca.Runtime.Interp.Machine.Calls.IndirectOperands
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Invariant.Rollback
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Store.Api.ObjectStaging
import Itasca.Runtime.Store.Initialization.SegmentOperations
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Integration.Api.GrowthAndValueSupport
import Itasca.Runtime.Interp.Relations.ResourceCausesAndArgumentErrors
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Integration.Api.GrowthAndHostResourceCauses
import Itasca.Runtime.Integration.Execution.Resources.SourceDemand
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Spec.BulkOperations
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Spec.Simd.ArithmeticMemoryAndFloat
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.SourceMachine.Stateful.TransitionInvariants
import Itasca.Runtime.SourceMachine.TransitionAndHostPreparation
import Itasca.Runtime.SourceMachine.Stateful.AccessAndGrowth
import Itasca.Runtime.SourceMachine.Simulation
import Itasca.Runtime.Spec.Simd.ConversionAndPacking
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.SourceMachine.Sim.Control
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.SourceMachine.Float.Descriptors
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.SourceMachine.Core.ProgressAndBounds
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.SourceMachine.Supported.CumulativeStep
import Itasca.Runtime.Interp.Calls.OutcomesAndResolution
import Itasca.Runtime.Store.Invariant.SourceAllocationLists

open WebAssembly

/-!
Proofs for Runtime / Integration / Api.

This module collects InvocationEntryResources, InvocationResourcesAdequate, StoreCreate, StoreGrow.
Each section documents its contracts and consumers.
-/

/-! ## InvocationEntryResources -/

section

/-! ## CertifiedApi -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std

/-- The retained component, body, module-map and export certificates imply
full generated source store typing; it is not an invariant field. -/
theorem CertifiedApiStore.source_typed {M : Type} {view : M → Slice U8}
    {code : Representation.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view code store) :
    Store_ok (Representation.decodeStore view code store) :=
  Store.decode_store_typed view code store certified.shape certified.storeSyntax
    certified.typed certified.segmentBounds certified.exportBounds

theorem CertifiedApiStore.update {M : Type} {view : M → Slice U8}
    {code : Representation.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedApiStore view code before)
    (mutation : CumulativeStoreMutation view code before after) :
    CertifiedApiStore view code after :=
  ⟨certified.toCertifiedSupportedStore.update mutation,
    certified.exportBounds.instances_eq mutation.metadata.instances⟩

theorem CertifiedApiStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Representation.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedApiStore view after store :=
  ⟨certified.toCertifiedSupportedStore.change_code agrees,certified.exportBounds⟩

theorem CertifiedApiStore.install_code {M : Type} {view : M → Slice U8}
    {code : Representation.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedApiStore view code store) (sources : List funccode) :
    CertifiedApiStore view (Store.installCode code store.instances.len.val sources) store :=
  certified.change_code (Store.install_code_agrees store code sources)

end Itasca.Integration

end

/-! ## ExecutableInv -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std

namespace ExecutableInv

theorem well_formed {M : Type} {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) :
    wf_store (Representation.decodeStore view code store) :=
  Store.decode_store_wf view code store held.shape held.storeSyntax

/-- Every store satisfying the public invariant has the generated semantic
store typing, including host functions. -/
theorem source_typed {M : Type} {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {store : runtime.store.Store M} (held : ExecutableInv view code store) :
    Store_ok (Representation.decodeStore view code store) :=
  held.toCertifiedApiStore.source_typed

theorem update {M : Type} {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {before after : runtime.store.Store M} (held : ExecutableInv view code before)
    (mutation : CumulativeStoreMutation view code before after) : ExecutableInv view code after :=
  ⟨held.toCertifiedApiStore.update mutation,
    mutation.segmentCounts.accounting mutation.metadata.instances held.segmentAccounting,
    held.capacities.metadata mutation.metadata.functions mutation.metadata.instances mutation.metadata.types mutation.metadata.identity⟩

end ExecutableInv
end Itasca.Integration

end

/-! ## ExecutableCallEntry -/

section

/-! Lookup evidence for an owned public function handle. This API-layer evidence
is shared by correspondence, typing and divergence; representation foundations
remain independent of public invocation setup. -/
namespace Itasca.Integration
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
    {code : Representation.CodeInterpretation} {store : runtime.store.Store M}
    (valid : ExecutableInv view code store) (address : runtime.FuncAddr)
    (issued : Store.ExternalIssued store (.Func address)) (owner : address.store = store.id) :
    ExecutableCallEntry store address := by
  have bound : address.index.val < store.funcs.val.length := issued owner
  let function := store.funcs.val[address.index.val]
  have hf : store.funcs.val[address.index.val]? = some function := List.getElem?_eq_getElem bound
  have signatureBound : function.signature.val < store.types.val.length :=
    (valid.shape.functions function (List.mem_of_getElem? hf)).1
  exact ⟨function,store.types.val[function.signature.val],hf,List.getElem?_eq_getElem signatureBound,signatureBound⟩
end Itasca.Integration

end

/-! ## InvocationEntryResources -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

theorem InvocationResourceCause.canonical {M P A : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M}
    {signature : Itasca.wasm_types.FuncType} {results : alloc.vec.Vec runtime.Value}
    {error : runtime.ExecError} (initial : config) (sourceStore : WebAssembly.store) (address : funcaddr)
    (cause : InvocationResourceCause allocator exec store signature results error) :
    CanonicalInvocationResourceCause allocator hooks initial sourceStore (Itasca.Translation.Environment.funcType signature) address
      store.limits.max_values.val store.limits.max_frames.val error := by
  rcases cause.kind with rfl | rfl
  · apply Or.inl
    simpa only [InvocationResourceCause,signatureWords,Itasca.Translation.Environment.funcType,typeSlots] using cause
  · apply Or.inl
    rcases cause with ⟨n,amount,refused⟩ | ⟨n,amount,refused⟩
    · exact Or.inl ⟨exec.slots,n,amount,refused⟩
    · exact Or.inr ⟨results,n,by simpa only [Itasca.Translation.Environment.funcType,List.length_map] using Nat.le_trans (Nat.le_of_eq amount) (Nat.sub_le _ _),refused⟩

theorem CallCause.invocation_canonical {M P A : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {prepared : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {signature : Itasca.wasm_types.FuncType} {error : runtime.ExecError}
    (view : M → Slice U8) (code : Representation.CodeInterpretation) (initial : config)
    (capacities : Representation.FunctionCapacities code store) (typed : CoreFunctionsTyped view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (hf : store.funcs.val[address.index.val]?=some function) (hw : function.code=.Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]?=some inst) (hc : inst.module.functions.val[functionIndex.val]?=some compiled)
    (empty : prepared.frames.val=[])
    (cause : CallCause allocator hooks prepared store platform 0#usize compiled error) :
    CanonicalInvocationResourceCause allocator hooks initial (Representation.decodeStore view code store)
      (Itasca.Translation.Environment.funcType signature) address.index.val store.limits.max_values.val store.limits.max_frames.val error := by
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
end Itasca.Integration

end

end

/-! ## InvocationResourcesAdequate -/

section

/-! ## InvocationObjectExclusion -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- Invocation does not allocate store objects. Every initial host failure is
setup/readback allocation, signature capacity, interrupt, or a host reply. -/
theorem InitialHostInvocationCause.no_objects {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.wasm_types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after (.Exhausted .Objects)) : False := by
  rcases cause with ⟨_,setup⟩ | ⟨impossible,_⟩ | ⟨prepared,p,called,_,_,_,_,failed,_,refused⟩
  · exact setup
  · cases impossible
  · simpa only [HostCallCauses,failed,HostPreparationCause] using refused

/-- A failed actual dispatch has no object-limit refusal branch. Store growth
instructions report their specified numeric failure result instead. -/
theorem EventfulDispatchCause.no_objects

    {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {expected : List valtype}
    {machine : EventfulMachine M P view code expected} {out}
    (cause : EventfulDispatchCause memory hooks floats allocator machine out (.Exhausted .Objects)) : False := by
  rcases cause with ordinary | host
  · have impossible := ordinary.1.kind
    simp at impossible
  · obtain ⟨failed,index,raw,pc,address,signature,base,identity,found,next,site,actual,refused⟩ := host
    simpa only [HostCallCauses,failed,HostPreparationCause] using refused
end Itasca.Integration

end

/-! ## InvocationResourcesAdequate -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Spec Itasca.Interp

/-- A conservative primitive allocation bound covering any representable
vector and additional request. This is independent of any invocation. -/
theorem reserve_ne_refusal_of_universal_bound {A T : Type} {allocator : runtime.platform.Alloc A}
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (values : alloc.vec.Vec T) (n : Usize) : allocator.reserve values n≠.ok (false,values) := by
  have fits : values.val.length+n.val≤2*Usize.max := by scalar_tac
  rw [available T values n fits]
  simp

end Itasca.Integration

end

end

/-! ## StoreCreate -/

section

open Itasca.Representation

/-! Shared store construction certificates. Allocation facts and retained
prefixes preserve structural shape; appending host functions preserves the
executable invariant and extends the decoded source store. Issued handles and
owned values persist under retained prefixes and cumulative mutations. -/

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Allocation facts complete the store shape when instance maps are unchanged. -/
theorem _root_.Itasca.Representation.Shape.of_allocated {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} (shape : Shape view before)
    (allocated : AllocationShape view after) (retained : StagedPrefix before after)
    (instances : after.instances = before.instances)
    (functions : ∀ function ∈ after.funcs.val, FunctionShape after function) :
    Shape view after := by
  refine ⟨allocated.identity, functions, allocated.memories, allocated.tables,
    allocated.globals, allocated.elements, ?_, allocated.canonicalTypes, ?_, ?_, ?_, ?_,
    allocated.signatureAccounting, allocated.signatureLimit, allocated.memoryAccounting,
    allocated.memoryLimit, allocated.tableAccounting, allocated.tableLimit⟩
  · intro inst member
    rw [instances] at member
    exact retained.instance_shape inst (shape.instances inst member)
  · have bound := allocated.objectLimit
    unfold objectCount at bound
    omega
  · simpa only [instances, retained.limits] using shape.instanceLimit
  · simpa only [instances, retained.instanceItems] using shape.instanceAccounting
  · simpa only [retained.instanceItems, retained.limits] using shape.instanceItemLimit

/-- Issued external handles remain valid when object vectors grow under the same identity. -/
theorem ExternalIssued.mono {M : Type} {before after : runtime.store.Store M}
    (identity : after.id = before.id)
    (functions : before.funcs.length ≤ after.funcs.length)
    (tables : before.tables.length ≤ after.tables.length)
    (memories : before.memories.length ≤ after.memories.length)
    (globals : before.globals.length ≤ after.globals.length)
    {external : runtime.Extern} (issued : ExternalIssued before external) :
    ExternalIssued after external := by
  cases external with
  | Func address => exact fun owner => Nat.lt_of_lt_of_le (issued (owner.trans identity)) functions
  | Table address => exact fun owner => Nat.lt_of_lt_of_le (issued (owner.trans identity)) tables
  | Memory address => exact fun owner => Nat.lt_of_lt_of_le (issued (owner.trans identity)) memories
  | Global address => exact fun owner => Nat.lt_of_lt_of_le (issued (owner.trans identity)) globals

/-- Issued reference values survive function and external identity vector growth. -/
theorem IssuedValue.mono {M : Type} {before after : runtime.store.Store M}
    (identity : after.id = before.id)
    (functions : before.funcs.length ≤ after.funcs.length)
    (externs : before.externs.length ≤ after.externs.length)
    {value : runtime.Value} (issued : IssuedValue before value) : IssuedValue after value := by
  cases value with
  | I32 _ | I64 _ | F32 _ | F64 _ | V128 _ => trivial
  | FuncRef address =>
    cases address with
    | none => trivial
    | some address => exact fun owner => Nat.lt_of_lt_of_le (issued (owner.trans identity)) functions
  | ExternRef address =>
    cases address with
    | none => trivial
    | some address => exact fun owner => Nat.lt_of_lt_of_le (issued (owner.trans identity)) externs

/-- Owned values retain their encoding bounds and ownership as address spaces grow. -/
theorem ValueInStore.mono {M : Type} {before after : runtime.store.Store M}
    (identity : after.id = before.id)
    (functions : before.funcs.length ≤ after.funcs.length)
    (externs : before.externs.length ≤ after.externs.length)
    {value : runtime.Value} (owned : ValueInStore before value) : ValueInStore after value := by
  refine ⟨by simpa only [identity] using owned.1, ?_⟩
  cases value with
  | I32 _ | I64 _ | F32 _ | F64 _ | V128 _ => trivial
  | FuncRef address =>
    cases address with
    | none => trivial
    | some address => exact Nat.lt_of_lt_of_le owned.2 functions
  | ExternRef address =>
    cases address with
    | none => trivial
    | some address => exact Nat.lt_of_lt_of_le owned.2 externs

private theorem retained_length {α : Type} (before after : alloc.vec.Vec α)
    (retained : after.val.take before.length = before.val) : before.length ≤ after.length := by
  have lengths := congrArg List.length retained
  simp only [List.length_take, alloc.vec.Vec.length] at lengths ⊢
  omega

/-- Retained prefixes preserve every issued external handle. -/
theorem StagedPrefix.external_issued {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {external : runtime.Extern}
    (issued : ExternalIssued before external) : ExternalIssued after external :=
  issued.mono retained.identity (retained_length _ _ retained.funcs)
    (retained_length _ _ retained.tables) (retained_length _ _ retained.memories)
    (retained_length _ _ retained.globals)

/-- Retained prefixes preserve issued reference values, including foreign ones. -/
theorem StagedPrefix.issued_value {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {value : runtime.Value}
    (issued : IssuedValue before value) : IssuedValue after value :=
  issued.mono retained.identity (retained_length _ _ retained.funcs)
    (by rw [retained.externs])

/-- Retained prefixes preserve owned and encodable API values. -/
theorem StagedPrefix.value_in_store {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {value : runtime.Value}
    (owned : ValueInStore before value) : ValueInStore after value :=
  owned.mono retained.identity (retained_length _ _ retained.funcs)
    (by rw [retained.externs])

end Itasca.Store

namespace Itasca.Integration
open Aeneas Aeneas.Std Store

/-- Retaining existing objects and adding only hosts preserves executable
certificates and extends the decoded source store. -/
theorem ExecutableInv.append_hosts {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {before after : runtime.store.Store M}
    (held : ExecutableInv view code before) (retained : StagedPrefix before after)
    (shape : Shape view after) (instances : after.instances = before.instances)
    (elements : after.elems = before.elems) (datas : after.datas = before.datas)
    (fresh : ∀ function ∈ after.funcs.val,
      function ∈ before.funcs.val ∨ ∃ id, function.code = .Host id) :
    ExecutableInv view code after ∧
      Extend_store (decodeStore view code before) (decodeStore view code after) := by
  have sourceSyntax := held.storeSyntax.instances_eq instances
  have wf := decode_store_wf view code after shape sourceSyntax
  obtain ⟨hf, hg, ht, hm, he, hd⟩ :=
    decode_store_prefix view code before after held.shape retained
  have extension := store_prefix_extends _ _ held.well_formed wf hf hg ht hm he hd
  have agrees : CodeAgreesOn before code code := fun _ _ _ _ => rfl
  refine ⟨{
    shape := shape, storeSyntax := sourceSyntax, typed := ?_, supported := ?_,
    compiled := ?_, segmentBounds := ?_, exportBounds := held.exportBounds.instances_eq instances,
    segmentAccounting := held.segmentAccounting.preserve elements datas instances,
    capacities := ?_ }, extension⟩
  · intro function member
    rcases fresh function member with old | ⟨id, host⟩
    · exact core_function_typed_prefix view code before after held.shape retained extension
        function old (held.typed function old)
    · simp only [Interp.CoreFunctionTyped, host]
      cases (decodeFunction code after function).TYPE with
      | mk_functype params results => cases params; cases results; constructor
  · intro function member
    obtain ⟨raw, present, rfl⟩ := List.mem_map.mp member
    rcases fresh raw present with old | ⟨id, host⟩
    · rw [decode_function_prefix code before after retained view held.shape raw old]
      exact held.supported _ (List.mem_map.mpr ⟨raw, old, rfl⟩)
    · simp only [decodeFunction, host]
  · intro function member
    rcases fresh function member with old | ⟨id, host⟩
    · exact supported_function_compiled_prefix held.shape retained agrees (held.compiled function old)
    · intro ii fi defined
      rw [host] at defined
      cases defined
  · exact ⟨by simpa only [elements] using held.segmentBounds.elements,
      by simpa only [datas] using held.segmentBounds.data⟩
  · intro function member
    rcases fresh function member with old | ⟨id, host⟩
    · exact (held.capacities function old).staged retained agrees
    · intro ii fi defined
      rw [host] at defined
      cases defined

/-- An empty store has executable certificates for every code interpretation.
The native wrapper supplies the positive identity: its counter starts at one
and advances with checked addition. That wrapper is outside extraction. -/
@[step] theorem _root_.Itasca.runtime.store.Store.with_identity.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Representation.CodeInterpretation) (id : Usize) (limits : runtime.store.StoreLimits)
    (positive : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits ⦃ store =>
      ExecutableInv view code store ∧ store.id = id ∧ store.limits = limits ∧
        Representation.decodeStore view code store = ⟨[], [], [], [], [], []⟩ ⦄ := by
  simp only [runtime.store.Store.with_identity, WP.spec_ok]
  refine ⟨?_, trivial, trivial, rfl⟩
  refine {
    shape := ?_, storeSyntax := ?_, typed := ?_, supported := ?_, compiled := ?_,
    segmentBounds := ?_, exportBounds := ?_, segmentAccounting := ?_, capacities := ?_ }
  · constructor <;>
      simp only [positive, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, List.map_nil, List.nodup_nil,
        alloc.vec.Vec.length, List.length_nil, add_zero, zero_le,
        UScalar.ofNatCore_val_eq, List.sum_nil, Slice.length]
  · simp only [StoreSyntax, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil,
      not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq, IsEmpty.forall_iff, implies_true]
  · simp only [Interp.CoreFunctionsTyped, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · simp only [SourceMachine.FunctionsSupported, decodeStore, alloc.vec.Vec.new,
      alloc.vec.Vec.from_val, List.map_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · simp only [Interp.Machine.CompiledFunctions, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · constructor <;> simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.not_mem_nil,
      alloc.vec.Vec.length, Nat.reducePow, IsEmpty.forall_iff, implies_true]
  · simp only [ExportBounds, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil,
      not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq, IsEmpty.forall_iff, implies_true]
  · constructor <;> simp only [alloc.vec.Vec.length, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
      List.length_nil, List.map_nil, List.sum_nil]
  · simp only [FunctionCapacities, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]

/-- Cumulative mutations retain all issued object addresses. Source extension
supplies table, memory, and global length monotonicity. -/
theorem CumulativeStoreMutation.external_issued {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {before after : runtime.store.Store M}
    (mutation : CumulativeStoreMutation view code before after) {external : runtime.Extern}
    (issued : ExternalIssued before external) : ExternalIssued after external := by
  obtain ⟨globals, memories, tables, functions, _, _⟩ := Spec.extend_store_objects mutation.extension
  apply issued.mono mutation.metadata.identity
  · rw [mutation.metadata.functions]
  · simpa only [decodeStore, List.length_map, alloc.vec.Vec.length] using tables.1
  · simpa only [decodeStore, List.length_map, alloc.vec.Vec.length] using memories.1
  · simpa only [decodeStore, List.length_map, alloc.vec.Vec.length] using globals.1

/-- Cumulative mutations retain both owned and foreign issued references. -/
theorem CumulativeStoreMutation.issued_value {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {before after : runtime.store.Store M}
    (mutation : CumulativeStoreMutation view code before after) {value : runtime.Value}
    (issued : IssuedValue before value) : IssuedValue after value :=
  issued.mono mutation.metadata.identity (by rw [mutation.metadata.functions])
    (by rw [mutation.externs])

/-- Cumulative mutations preserve owned API values and their encoding bounds. -/
theorem CumulativeStoreMutation.value_in_store {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {before after : runtime.store.Store M}
    (mutation : CumulativeStoreMutation view code before after) {value : runtime.Value}
    (owned : ValueInStore before value) : ValueInStore after value :=
  owned.mono mutation.metadata.identity (by rw [mutation.metadata.functions])
    (by rw [mutation.externs])

end Itasca.Integration

end

/-! ## StoreGrow -/

section

open Itasca.Representation

/-! Public growth follows the source growth judgments. Private append witnesses
establish those effects and the total source bytes/references remain within quotas. -/

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Representation WebAssembly

theorem memory_grown_of_effect {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (index : Usize) (delta pages : U32)
    (shape : Shape view before) (effect : MemoryGrowth view code before index delta (pages, after)) :
    MemoryGrown (decodeStore view code before) (decodeStore view code after) index.val delta.val pages.val := by
  rcases effect with ⟨failed,same,_⟩ | ⟨old,buffer,count,lookup,bytes,_,_,capacity,maximum,size,changed⟩
  · refine Or.inl ⟨?_,same⟩
    simpa only [core.num.U32.MAX,UScalar.ofNatCore_val_eq,U32.max_eq,U32.rMax] using congrArg UScalar.val failed
  · refine Or.inr ⟨decodeMemory view old,decodeMemory view {old with buf:=buffer},?_,
      decode_memory_growth view old buffer delta (shape.memories old (List.mem_of_getElem? lookup)) bytes capacity maximum,?_,?_⟩
    · simp only [decodeStore,List.getElem?_map,lookup,Option.map_some]
    · simpa only [decodeMemory,decodeBytes,List.length_map] using size
    · dsimp only at changed
      rw [changed]
      simp only [decodeStore,alloc.vec.Vec.set_val_eq,List.map_set]
      rfl

theorem table_grown_of_effect {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (index : Usize) (delta size : U32)
    (value : val) (word : U64)
    (reference : ∀ old, before.tables.val[index.val]? = some old → val_ref (decodeRef old.ty word) = value)
    (effect : TableGrowth before index delta word (size, after)) :
    TableGrown (decodeStore view code before) (decodeStore view code after) index.val delta.val size.val value := by
  rcases effect with ⟨failed,same⟩ | ⟨old,elements,count,lookup,words,capacity,_,_,maximum,changed⟩
  · refine Or.inl ⟨?_,congrArg (decodeStore view code) same⟩
    simpa only [core.num.U32.MAX,UScalar.ofNatCore_val_eq,U32.max_eq,U32.rMax] using congrArg UScalar.val failed
  · have sizeEq := congrArg Prod.fst changed
    have afterEq := congrArg Prod.snd changed
    dsimp only at sizeEq afterEq
    refine Or.inr ⟨decodeTable old,decodeTable {old with elements},decodeRef old.ty word,?_,reference old lookup,
      decode_table_growth old elements delta word words capacity maximum,?_,?_⟩
    · simp only [decodeStore,List.getElem?_map,lookup,Option.map_some]
    · rw [sizeEq]
      simp only [UScalar.cast_val_eq,alloc.vec.Vec.len_val,decodeTable,List.length_map]
      scalar_tac
    · rw [afterEq]
      simp only [decodeStore,alloc.vec.Vec.set_val_eq,List.map_set]
      rfl
end Itasca.Store

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Representation

theorem decoded_memory_quota {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (shape : Shape view store) :
    ((decodeStore view code store).MEMS.map fun object => object.BYTES.length).sum ≤ store.limits.max_memory_bytes.val := by
  simpa only [decodeStore,List.map_map,Function.comp_def,decodeMemory,decodeBytes,List.length_map,
    ←shape.memoryAccounting] using shape.memoryLimit

theorem decoded_table_quota {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (shape : Shape view store) :
    ((decodeStore view code store).TABLES.map fun object => object.REFS.length).sum ≤ store.limits.max_table_elements.val := by
  simpa only [decodeStore,List.map_map,Function.comp_def,decodeTable,List.length_map,
    ←shape.tableAccounting] using shape.tableLimit
end Itasca.Store

namespace Itasca.Integration
open Aeneas Aeneas.Std Store

/-- Memory growth preserves executable stores, including the failure sentinel. -/
@[step] theorem _root_.Itasca.runtime.store.Store.grow_memory_with.spec {M : Type}
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
          MemoryGrown (decodeStore view code store) (decodeStore view code after)
            address.index.val delta.val pages.val ∧
          ((decodeStore view code after).MEMS.map fun object => object.BYTES.length).sum ≤ store.limits.max_memory_bytes.val ⦄ := by
  unfold runtime.store.Store.grow_memory_with
  step with runtime.store.Store.check.spec memory store address.store as ⟨checkedStore, checkedStoreEq⟩
  rw [checkedStoreEq]
  by_cases owner : address.store = store.id
  · simp only [if_pos owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have inside := issued owner
    step with memory_grow_effect memory view laws code store address.index delta inside
      (fun object member => (held.shape.memories object member).length_bound)
      (fun object member => (held.shape.memories object member).1)
      as ⟨pages, after, effect⟩
    have extension := effect.extends view code store held.shape held.storeSyntax
      address.index delta inside (pages, after)
    have mutation := memory_growth_cumulative_mutation_of_shape held.shape held.storeSyntax
      held.segmentBounds inside effect extension
    refine ⟨held.update mutation, mutation, owner,
      memory_grown_of_effect view code store after address.index delta pages held.shape effect, ?_⟩
    have limits : after.limits = store.limits := mutation.limits
    simpa only [limits] using decoded_memory_quota view code after mutation.shape
  · simp only [if_neg owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨held, .refl_of_shape held.shape held.storeSyntax held.segmentBounds, rfl, owner, rfl⟩

/-- Table growth checks ownership and reference type before extending the table. -/
@[step] theorem _root_.Itasca.runtime.store.Store.grow_table_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (delta : U32) (value : runtime.Value)
    (issued : ExternalIssued store (.Table address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.grow_table_with memory allocator store address delta value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err error => after = store ∧ (error = .WrongStore ∨ error = .BadArguments)
      | .Ok size => address.store = store.id ∧
          TableGrown (decodeStore view code store) (decodeStore view code after)
            address.index.val delta.val size.val (sourceValue value) ∧
          ((decodeStore view code after).TABLES.map fun object => object.REFS.length).sum ≤ store.limits.max_table_elements.val ⦄ := by
  classical
  unfold runtime.store.Store.grow_table_with
  step with runtime.store.Store.check.spec memory store address.store as ⟨checkedStore, checkedStoreEq⟩
  rw [checkedStoreEq]
  by_cases owner : address.store = store.id
  · simp only [if_pos owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.check_value_eq memory store value as ⟨checked, checkedEq⟩
    rw [checkedEq]
    by_cases valueOwner : Interp.OwnedBy store.id value
    · simp only [Interp.checkOwner, if_pos valueOwner,
        core.result.Result.Insts.CoreOpsTry.branch, bind_ok, value_type_exact]
      have inside := issued owner
      step as ⟨table, tableEq⟩
      simp only [element_value_type_exact, Interp.value_type_ne_eq, bind_ok]
      by_cases matching : Representation.rawType value = elementValueType table.ty
      · simp only [if_pos matching, Bool.false_eq_true, ite_false]
        obtain ⟨words, encoded, reference⟩ := WP.spec_imp_exists
          (encode_reference_shape store value table.ty matching.symm (valueIssued.in_store valueOwner))
        cases words with
        | mk lo hi =>
          change ReferenceShape store table.ty lo at reference
          rw [encoded, bind_ok]
          step with table_grow_effect memory allocator law store address.index delta lo inside
            (fun object member => (held.shape.tables object member).1)
            as ⟨size, after, effect⟩
          have owned : ReferenceShape store (store.tables.val[address.index.val]).ty lo := by
            simpa only [tableEq] using reference
          have extension := effect.extends view code store held.shape held.storeSyntax
            address.index delta lo inside owned (size, after)
          have mutation := table_growth_cumulative_mutation_of_shape held.shape held.storeSyntax
            held.segmentBounds inside owned effect extension
          have decoded := decode_encoded_value store value (valueIssued.in_store valueOwner) (lo,hi) encoded
          rw [matching] at decoded
          have sourceRef : val_ref (decodeRef table.ty lo) = sourceValue value := by
            cases kind : table.ty <;> simpa only [kind,elementValueType,decodeWords,ref_val_eq] using decoded
          have found : store.tables.val[address.index.val]? = some table := by
            simpa only [tableEq] using List.getElem?_eq_getElem inside
          refine ⟨held.update mutation, mutation, owner, ?_, ?_⟩
          · apply table_grown_of_effect view code store after address.index delta size (sourceValue value) lo ?_ effect
            intro old lookup
            have same : old = table := Option.some.inj (lookup.symm.trans found)
            subst old
            exact sourceRef
          · have limits : after.limits = store.limits := mutation.limits
            simpa only [limits] using decoded_table_quota view code after mutation.shape
      · simp only [if_neg matching, ite_true, WP.spec_ok]
        exact ⟨held, .refl_of_shape held.shape held.storeSyntax held.segmentBounds,
          rfl, Or.inr rfl⟩
    · simp only [Interp.checkOwner, if_neg valueOwner,
        core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact ⟨held, .refl_of_shape held.shape held.storeSyntax held.segmentBounds,
        rfl, Or.inl rfl⟩
  · simp only [if_neg owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨held, .refl_of_shape held.shape held.storeSyntax held.segmentBounds,
      rfl, Or.inl rfl⟩

end Itasca.Integration

end
