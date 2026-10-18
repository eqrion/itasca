import Exec.Interp.StructuredMachine.FrameStack
import Exec.Interp.Relations.StackPreservation
import Exec.Interp.Relations.PrefixEffect
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
variable {emission : FunctionEmission}

/-- A checked ordinary mutation preserves the full caller chain through both
source store extension and exact concrete metadata/prefix preservation. -/
theorem FrameStackRel.step_active {M : Type} {oldStore newStore : runtime.store.Store M}
    {oldSourceStore newSourceStore : _root_.store}
    {before after : runtime.interp.Execution} {source updatedSource : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel emission oldStore oldSourceStore before (source :: rest))
    (metadata : FrameStoreMetadata oldStore newStore) (extension : Extend_store oldSourceStore newSourceStore)
    (raw updated : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    (frames : after.frames.val = before.frames.val.dropLast ++ [updated])
    (sameBase : updated.base = raw.base) (sameReturns : updatedSource.resultTypes = source.resultTypes)
    (identity : after.store = before.store) (capacity : before.slots.length ≤ after.slots.length)
    (preserve : ∀ position bits, WordsAt before.slots.val position bits →
      position + bits.length ≤ raw.base.val → WordsAt after.slots.val position bits)
    (active : ActiveFrame emission newStore newSourceStore after updated updatedSource) :
    FrameStackRel emission newStore newSourceStore after (updatedSource :: rest) := by
  have transported := relation.store_extension metadata extension
  cases transported with
  | @active actual _ raws _ oldFrames oldActive saved =>
    have same : actual = raw := by simpa only [oldFrames,List.getLast?_concat,Option.some.injEq] using top
    subst actual
    have remaining : before.frames.val.dropLast = raws.reverse := by rw [oldFrames,List.dropLast_concat]
    apply FrameStackRel.active (raw := updated) (raws := raws)
    · simpa only [remaining] using frames
    · exact active
    · rw [sameReturns,sameBase]
      apply saved.transport
      · intro frame source binding member
        apply binding.retain identity _ capacity
        rw [frames,remaining]
        exact List.mem_append_left _ (List.mem_reverse.mpr member)
      · exact preserve

theorem FrameStackRel.single_base {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame}
    (relation : FrameStackRel emission store sourceStore exec [source])
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw) : raw.base.val = 0 := by
  cases relation with
  | @active actual _ raws _ frames active saved =>
    have same : actual = raw := by simpa only [frames,List.getLast?_concat,Option.some.injEq] using top
    subst actual
    exact saved.empty_inv.2

end Exec.Interp.StructuredMachine
