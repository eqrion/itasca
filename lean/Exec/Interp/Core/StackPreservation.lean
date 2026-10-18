import Exec.Interp.StructuredMachine.CoreAdapter
import Exec.Interp.StructuredMachine.StackPreservation
import Exec.Interp.Core.FrameStack
import Exec.Interp.Relations.StackPreservation
import Exec.Interp.Relations.PrefixEffect
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A checked ordinary mutation preserves the full caller chain through both
source store extension and exact concrete metadata/prefix preservation. -/
theorem CoreFrameStackRel.step_active {M : Type} {oldStore newStore : runtime.store.Store M}
    {oldSourceStore newSourceStore : _root_.store}
    {before after : runtime.interp.Execution} {source updatedSource : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : CoreFrameStackRel oldStore oldSourceStore before (source :: rest))
    (metadata : FrameStoreMetadata oldStore newStore) (extension : Extend_store oldSourceStore newSourceStore)
    (raw updated : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    (frames : after.frames.val = before.frames.val.dropLast ++ [updated])
    (sameBase : updated.base = raw.base) (sameReturns : updatedSource.resultTypes = source.resultTypes)
    (identity : after.store = before.store) (capacity : before.slots.length ≤ after.slots.length)
    (preserve : ∀ position bits, WordsAt before.slots.val position bits →
      position + bits.length ≤ raw.base.val → WordsAt after.slots.val position bits)
    (active : CoreActiveFrame newStore newSourceStore after updated updatedSource) :
    CoreFrameStackRel newStore newSourceStore after (updatedSource :: rest) := by
  apply StructuredMachine.CoreAdapter.stack_iff.mpr
  exact StructuredMachine.FrameStackRel.step_active
    (StructuredMachine.CoreAdapter.stack_iff.mp relation)
    metadata extension raw updated top frames sameBase sameReturns identity capacity preserve
    (StructuredMachine.CoreAdapter.active_iff.mp active)

theorem CoreFrameStackRel.single_base {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame}
    (relation : CoreFrameStackRel store sourceStore exec [source])
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw) : raw.base.val = 0 := by
  exact StructuredMachine.FrameStackRel.single_base
    (StructuredMachine.CoreAdapter.stack_iff.mp relation) raw top

end Exec.Interp
