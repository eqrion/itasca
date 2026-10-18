import Exec.Interp.StructuredMachine.PrepareCallStack
import Exec.Interp.StructuredMachine.HostSavedFramesResume
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
variable {emission : FunctionEmission}

/-- Actual caller PC advancement and checked host result writes compose into
the full resumed concrete stack under retained raw metadata and source extension. -/
theorem FrameStackRel.host_call_return {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel emission store s exec (source :: rest))
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint emission s raw source compiled C targets next output)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Code.slots ((source.locals ++ front).map Code.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Code.valueType ++ returns) after pc.val next output)
    (afterStore : runtime.store.Store M) (sourceAfter : _root_.store)
    (retained : FrameStorePrefix store afterStore) (bounds : FrameTypeBounds store)
    (extension : Extend_store s sourceAfter)
    (finished : runtime.interp.Execution) (values : List val)
    (effect : HostReturnEffect {exec with frames := exec.frames.set index {raw with pc := pc}} finished base values)
    (typed : values.map Code.valueType = returns) :
    FrameStackRel emission afterStore sourceAfter finished
      ({source with code := after,vals := front ++ values} :: rest) ∧
      ReadyTop emission afterStore sourceAfter finished {source with code := after,vals := front ++ values} := by
  obtain ⟨raws,frames,saved⟩ := relation.prepare_call raw index pc last lookup binding slots program point
    front args after returns base split destination heights continuation
  exact saved.resume_host_extended retained bounds extension frames effect typed heights

end Exec.Interp.StructuredMachine
