import Itasca.Runtime.Interp.Machine.Frames.FrameStack
import Itasca.Runtime.Interp.Calls.CallStack

/-!
The caller's post-fetch continuation and live prefix form the saved frame needed for entry. The argument words remain available to the new callee.

Main declarations: `prepare_saved_caller` and `FrameStackRel.call_enter`. A direct consumer is `Interp.Machine.Calls.CallStackEntry`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- The caller's post-fetch continuation and live prefix form the saved frame
needed for entry. The argument words remain available to the new callee. -/
theorem prepare_saved_caller {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw source compiled C targets next output)
    (index : Usize) (pc : U32) (lookup : exec.frames.val[index.val]? = some raw)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Compiler.slots ((source.locals ++ front).map Compiler.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Compiler.valueType ++ returns) after pc.val next output) :
    SavedFrame store s { exec with frames := exec.frames.set index { raw with pc := pc } }
      { raw with pc := pc } { source with vals := front, code := after } returns base := by
  refine ⟨binding.advance index pc lookup, ?_, destination,
    compiled, C, targets, next, output, ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩,
    point.suspend front args after pc returns split heights continuation⟩
  apply WordsAt.append_left (right := Compiler.encodeValues args)
  simpa only [FrameSlots, ValuesAt, split, Compiler.encode_values_append, List.append_assoc] using slots

/-- After successful entry, the initialized callee and prepared caller chain
constitute the complete frame-stack relation. -/
theorem FrameStackRel.call_enter {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {before after : runtime.interp.Execution} {raws : List runtime.interp.Frame} {sources : List SourceMachine.AFrame}
    {instanceIndex functionIndex base : Usize} {compiled : runtime.bytecode.CompiledFunction}
    (effect : CallEntryEffect before after instanceIndex functionIndex base compiled)
    (source : SourceMachine.AFrame)
    (frames : before.frames.val = raws.reverse)
    (saved : SavedFrames store s before raws sources source.resultTypes base.val)
    (active : ActiveFrame store s after ⟨instanceIndex, functionIndex, 0#u32, base⟩ source)
    (params : compiled.param_slots.val ≤ compiled.local_slots.val)
    (capacity : compiled.local_slots.val ≤ compiled.slot_count.val) :
    FrameStackRel store s after (source :: sources) := by
  exact .active (by rw [effect.1, frames]) active
    (saved.call_preserved effect (Nat.le_refl _) params capacity)

end Itasca.Runtime.Interp.Machine
