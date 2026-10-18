import Exec.Interp.StructuredMachine.StackPreservation
import Exec.Interp.Calls.ReturnRefinement
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
variable {emission : FunctionEmission}

/-- Returning to a suspended caller restores the active certificate and
preserves the older caller chain. -/
theorem FrameStackRel.return_to_caller_ready {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {callee caller : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel emission store sourceStore before (callee :: caller :: rest))
    (raw : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    {src count : Nat} (effect : ReturnEffect before after raw.base.val src count)
    (results : List val)
    (represented : ValuesAt before.slots.val (raw.base.val + src) results)
    (types : results.map Code.valueType = callee.resultTypes)
    (width : count = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val + src + count ≤ before.slots.length)
    (heights : Abs.FrameHeights caller) :
    FrameStackRel emission store sourceStore after ({ caller with vals := caller.vals ++ results } :: rest) ∧
      ReadyTop emission store sourceStore after { caller with vals := caller.vals ++ results } := by
  cases relation with
  | @active actual _ raws _ frames active saved =>
    have same : actual = raw := by simpa only [frames, List.getLast?_concat, Option.some.injEq] using top
    subst actual
    cases saved with
    | @cons callerRaw older _ _ _ _ head tail =>
      have remaining : before.frames.val.dropLast = older.reverse ++ [callerRaw] := by
        rw [frames, List.dropLast_concat]
        simp only [List.reverse_cons]
      have member : callerRaw ∈ before.frames.val.dropLast := by rw [remaining]; simp
      obtain ⟨binding, slots, compiled, C, targets, next, output, program, point⟩ :=
        head.resume effect member results represented types width bounds heights
      constructor
      · apply FrameStackRel.active
        · simpa only [List.reverse_cons] using effect.frames frames
        · exact ⟨binding, slots, compiled, C, targets, next, output, false, program, .ready point⟩
        · apply tail.return_preserved effect head.base_le _ bounds
          intro frame found
          rw [remaining]
          exact List.mem_append_left _ (List.mem_reverse.mpr found)
      · refine ⟨callerRaw, compiled, C, targets, next, output, ?_, program, point⟩
        rw [effect.frames frames]
        simp

theorem FrameStackRel.return_to_caller {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {callee caller : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel emission store sourceStore before (callee :: caller :: rest))
    (raw : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    {src count : Nat} (effect : ReturnEffect before after raw.base.val src count)
    (results : List val)
    (represented : ValuesAt before.slots.val (raw.base.val + src) results)
    (types : results.map Code.valueType = callee.resultTypes)
    (width : count = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val + src + count ≤ before.slots.length)
    (heights : Abs.FrameHeights caller) :
    FrameStackRel emission store sourceStore after ({ caller with vals := caller.vals ++ results } :: rest) := by
  exact (relation.return_to_caller_ready raw top effect results represented types width bounds heights).1

/-- The last return removes the concrete frame stack completely. -/
theorem FrameStackRel.return_final {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {callee : Abs.AFrame}
    (relation : FrameStackRel emission store sourceStore before [callee])
    {base src count : Nat} (effect : ReturnEffect before after base src count) :
    FrameStackRel emission store sourceStore after [] := by
  cases relation with
  | active frames active saved =>
    obtain ⟨empty, _⟩ := saved.empty_inv
    apply FrameStackRel.empty
    simpa only [empty, List.reverse_nil] using effect.frames frames

theorem FrameStackRel.return_complete {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {callee : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel emission store sourceStore before (callee :: rest))
    (ambient : frame)
    (raw : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    {src count : Nat} (effect : ReturnEffect before after raw.base.val src count)
    (results : List val)
    (represented : ValuesAt before.slots.val (raw.base.val + src) results)
    (types : results.map Code.valueType = callee.resultTypes)
    (width : count = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val + src + count ≤ before.slots.length)
    (heights : ∀ caller ∈ rest, Abs.FrameHeights caller) :
    FrameStackRel emission store sourceStore after (returnedState sourceStore ambient rest results).frames ∧
      ReadyState emission store after (returnedState sourceStore ambient rest results) := by
  cases rest with
  | nil =>
    refine ⟨relation.return_final effect, ?_⟩
    have base := relation.single_base raw top
    simpa only [ReadyState, returnedState, base] using effect.results represented width bounds
  | cons caller rest =>
    exact relation.return_to_caller_ready raw top effect results represented types width bounds
      (heights caller (by simp))

end Exec.Interp.StructuredMachine
