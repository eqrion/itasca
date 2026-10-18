import Exec.Interp.Relations.SourceValueCauses
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Actual allocator refusals at entry retain source-bounded request sizes. -/
theorem CallCause.source_allocation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {base : Usize}
    {compiled : runtime.bytecode.CompiledFunction} {words : Nat}
    (bound : compiled.slot_count.val ≤ words)
    (cause : CallCause allocator hooks exec store platform base compiled (.Exhausted .Allocation)) :
    (∃ n : Usize, n.val ≤ base.val + words ∧ allocator.reserve exec.slots n = .ok (false, exec.slots)) ∨
      allocator.reserve exec.frames 1#usize = .ok (false, exec.frames) := by
  rcases cause with ⟨needed, n, amount, refused⟩ | refused
  · exact Or.inl ⟨n, by omega, refused⟩
  · exact Or.inr refused

/-- An allocator refusal for source call storage. The witness retains the
actual request; its upper bound contains only decoded source quantities. -/
def SourceCallAllocation {A : Type} (allocator : runtime.platform.Alloc A)
    (source : Abs.AState) : Prop :=
  ∃ address base words, SourceCallSite source address base ∧
    SourceFunctionCapacity source.store address words ∧
    ((∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val ≤ base + words ∧
        allocator.reserve slots n = .ok (false, slots)) ∨
      ∃ frames : alloc.vec.Vec runtime.interp.Frame,
        allocator.reserve frames 1#usize = .ok (false, frames))

theorem SourceDirectCallCause.source_allocation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.Instance}
    {compiled : runtime.bytecode.CompiledFunction} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (cause : SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source (.Exhausted .Allocation)) :
    SourceCallAllocation allocator source := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, codeObject, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  obtain ⟨words, capacity, bound⟩ := function_capacity_decoded view code store capacities address function
    instanceIndex functionIndex callee codeObject lookup wasm instanceLookup codeLookup
  refine ⟨address.index.val, base.val, words, site, by simpa only [decoded] using capacity, ?_⟩
  rcases rejection with ⟨needed, n, amount, refused⟩ | refused
  · exact Or.inl ⟨exec.slots, n, by omega, refused⟩
  · exact Or.inr ⟨exec.frames.set index {raw with pc := pc}, refused⟩

theorem SliceFailure.source_allocation {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (failure : SliceFailure allocator hooks exec store platform source (.Exhausted .Allocation)) :
    SourceCallAllocation allocator source := by
  rcases failure with ⟨⟨trap, kind, _⟩, _⟩ | ⟨kind, _⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    exact cause.source_allocation view code decoded capacities

theorem SourceCallAllocation.prepend {A : Type} {allocator : runtime.platform.Alloc A}
    {before middle : Abs.AState} {count : Nat}
    (steps : Spec.StepsHN count (Abs.decode before) [] (Abs.decode middle))
    (sameStore : middle.store = before.store) (sameAmbient : middle.ambient = before.ambient)
    (cause : SourceCallAllocation allocator middle) : SourceCallAllocation allocator before := by
  obtain ⟨address, base, words, site, capacity, refused⟩ := cause
  exact ⟨address, base, words, site.prepend steps sameStore sameAmbient,
    by simpa only [sameStore] using capacity, refused⟩

theorem SliceLoopOutcome.source_allocation {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound}
    {result : ExecutionResult M P}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : sourceStore = Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (outcome : SliceLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err (.Exhausted .Allocation)) :
    SourceCallAllocation allocator initial.source := by
  obtain ⟨previous, dispatches, count, finalExec, finalPlatform, run, steps, cost, actual, failure, returned⟩ :=
    outcome.error_reachable failed
  exact (failure.source_allocation view code (previous.decoded.trans decoded) capacities).prepend steps
    (previous.decoded.trans initial.decoded.symm) (previous.ambient_eq.trans initial.ambient_eq.symm)
end Exec.Interp
