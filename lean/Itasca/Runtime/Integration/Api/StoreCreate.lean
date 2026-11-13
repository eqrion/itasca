import Itasca.Runtime.Integration.Api.InvocationEntryResources
import Itasca.Runtime.Store.Invariant.SourceAllocationLists
import Itasca.Runtime.Store.Invariant.ErrorPost
import Itasca.Runtime.Store.Invariant.FunctionCapacities

/-! Shared store construction certificates. Allocation facts and retained
prefixes preserve structural shape; appending host functions preserves the
executable invariant and extends the decoded source store. -/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Allocation facts complete the store shape when instance maps are unchanged. -/
theorem Shape.of_allocated {M : Type} {view : M → Slice U8}
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

end Itasca.Runtime.Store

namespace Itasca.Runtime.Integration
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
    (code : Store.CodeInterpretation) (id : Usize) (limits : runtime.store.StoreLimits)
    (positive : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits ⦃ store =>
      ExecutableInv view code store ∧ store.id = id ∧ store.limits = limits ∧
        Store.decodeStore view code store = ⟨[], [], [], [], [], []⟩ ⦄ := by
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

end Itasca.Runtime.Integration
