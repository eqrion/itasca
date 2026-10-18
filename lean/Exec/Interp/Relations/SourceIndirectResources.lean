import Exec.Interp.Relations.SourceCanonicalCapacity
import Exec.Interp.Relations.SourceIndirectSite
import Exec.Interp.Relations.SourceAllocationCauses
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A selected call may be direct or table-resolved; either witness is purely
source-level and fixes the shared argument base. -/
def SourceInvocationSite (source : Abs.AState) (address : funcaddr) (base : Nat) : Prop :=
  SourceCallSite source address base ∨ SourceIndirectCallSite source address base

def SourceInvocationAllocation {A : Type} (allocator : runtime.platform.Alloc A)
    (source : Abs.AState) : Prop :=
  ∃ address base words, SourceInvocationSite source address base ∧
    SourceCanonicalFunctionCapacity source.store address words ∧
    ((∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val ≤ base+words ∧
      allocator.reserve slots n=.ok (false,slots)) ∨
      ∃ frames : alloc.vec.Vec runtime.interp.Frame, allocator.reserve frames 1#usize=.ok (false,frames))

theorem SourceIndirectCallCause.source_values {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {interpretation : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {index : Usize} {raw : runtime.interp.Frame} {compiled : runtime.bytecode.CompiledFunction} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (cause : SourceIndirectCallCause allocator hooks interpretation exec store platform index raw compiled source (.Exhausted .Values)) :
    ∃ address base words, SourceIndirectCallSite source address base ∧
      SourceCanonicalFunctionCapacity source.store address words ∧ store.limits.max_values.val<base+words := by
  obtain ⟨pc,address,base,function,ii,fi,inst,callee,found,defined,hi,hc,rejected,site⟩ := cause.source_site view code decoded
  obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities typed {store:=store.id,index:=address}
    function ii fi inst callee found defined hi hc
  refine ⟨address.val,base.val,words,site,by simpa only [decoded] using capacity,?_⟩
  change store.limits.max_values.val<base.val+callee.slot_count.val at rejected
  omega

theorem SourceIndirectCallCause.source_allocation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {interpretation : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {index : Usize} {raw : runtime.interp.Frame} {compiled : runtime.bytecode.CompiledFunction} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (cause : SourceIndirectCallCause allocator hooks interpretation exec store platform index raw compiled source (.Exhausted .Allocation)) :
    SourceInvocationAllocation allocator source := by
  obtain ⟨pc,address,base,function,ii,fi,inst,callee,found,defined,hi,hc,rejected,site⟩ := cause.source_site view code decoded
  obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities typed {store:=store.id,index:=address}
    function ii fi inst callee found defined hi hc
  refine ⟨address.val,base.val,words,Or.inr site,by simpa only [decoded] using capacity,?_⟩
  rcases CallCause.source_allocation bound rejected with ⟨n,amount,refused⟩ | refused
  · exact Or.inl ⟨exec.slots,n,amount,refused⟩
  · exact Or.inr ⟨exec.frames.set index {raw with pc:=pc},refused⟩
theorem SourceDirectCallCause.source_values_canonical {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.Instance}
    {compiled : runtime.bytecode.CompiledFunction} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (cause : SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source (.Exhausted .Values)) :
    ∃ address base words, SourceCallSite source address base ∧
      SourceCanonicalFunctionCapacity source.store address words ∧ store.limits.max_values.val < base + words := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, codeObject, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  obtain ⟨words, capacity, bound⟩ := function_canonical_capacity_decoded view code store capacities typed address function
    instanceIndex functionIndex callee codeObject lookup wasm instanceLookup codeLookup
  refine ⟨address.index.val, base.val, words, site, by simpa only [decoded] using capacity, ?_⟩
  change store.limits.max_values.val < base.val + codeObject.slot_count.val at rejection
  omega

theorem SourceDirectCallCause.source_allocation_canonical {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.Instance}
    {compiled : runtime.bytecode.CompiledFunction} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (cause : SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source (.Exhausted .Allocation)) :
    SourceInvocationAllocation allocator source := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, codeObject, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  obtain ⟨words, capacity, bound⟩ := function_canonical_capacity_decoded view code store capacities typed address function
    instanceIndex functionIndex callee codeObject lookup wasm instanceLookup codeLookup
  refine ⟨address.index.val, base.val, words, Or.inl site, by simpa only [decoded] using capacity, ?_⟩
  rcases rejection with ⟨needed, n, amount, refused⟩ | refused
  · exact Or.inl ⟨exec.slots, n, by omega, refused⟩
  · exact Or.inr ⟨exec.frames.set index {raw with pc := pc}, refused⟩

end Exec.Interp
