import Exec.Interp.StructuredMachine.FloatCoreAdapter
import Exec.Interp.StructuredMachine.OrdinaryStack
import Exec.Interp.FloatCore.StackPreservation
import Exec.Interp.FloatCore.Execution
import Exec.Interp.Control.SkipStack
import Exec.Interp.Relations.PrefixDispatch

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Ordinary bytecode changes only the active source's live values and code.
Its observed prefix law preserves all suspended frames at once. -/
theorem FloatCoreFrameStackRel.ordinary {M : Type} {store nextStore : runtime.store.Store M}
    {sourceStore nextSourceStore : _root_.store}
    {exec after : runtime.interp.Execution} {source updatedSource : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FloatCoreFrameStackRel store sourceStore exec (source :: rest))
    (stores : FrameStoreMetadata store nextStore) (extension : Extend_store sourceStore nextSourceStore)
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    {compiled C targets next output pending}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS)
    (point : FloatCoreControlPoint nextSourceStore { raw with pc := pc } updatedSource compiled C targets next output pending)
    (slots : FrameSlots after { raw with pc := pc } updatedSource)
    (metadata : FrameMetadata source updatedSource)
    (effect : { after with slots := exec.slots } =
      { exec with frames := exec.frames.set index { raw with pc := pc } })
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val) :
    FloatCoreFrameStackRel nextStore nextSourceStore after (updatedSource :: rest) := by
  apply StructuredMachine.FloatCoreAdapter.stack_iff.mpr
  exact (StructuredMachine.FloatCoreAdapter.stack_iff.mp relation).ordinary stores extension raw index pc last lookup
    binding program (StructuredMachine.FloatCoreAdapter.control_iff.mp point) slots metadata effect preserved

end Exec.Interp
