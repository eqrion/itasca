import Exec.Interp.Relations.StackRelation

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Updating the active PC retains the frame's metadata and allocated region. -/
theorem FrameBinding.advance {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source) (index : Usize) (pc : U32)
    (lookup : exec.frames.val[index.val]? = some raw) :
    FrameBinding store { exec with frames := exec.frames.set index { raw with pc := pc } }
      { raw with pc := pc } source := by
  obtain ⟨inst, fn, compiled, signature, identity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, identity, ?_, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩
  have within := (List.getElem?_eq_some_iff.mp lookup).1
  simp only [alloc.vec.Vec.set_val_eq]
  apply List.mem_of_getElem? (i := index.val)
  simp [within]

/-- Fetch changes only the last frame's PC. All older frame bindings survive. -/
theorem FrameBinding.advance_older {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source) (index : Usize) (updated : runtime.interp.Frame)
    (last : index.val + 1 = exec.frames.length)
    (older : raw ∈ exec.frames.val.dropLast) :
    FrameBinding store { exec with frames := exec.frames.set index updated } raw source := by
  obtain ⟨inst, fn, compiled, signature, identity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, identity, ?_, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩
  simp only [alloc.vec.Vec.set_val_eq]
  have kept : (exec.frames.val.set index.val updated).dropLast = exec.frames.val.dropLast := by
    rw [List.dropLast_eq_take, List.length_set, List.take_set_of_le (by change exec.frames.length - 1 ≤ index.val; omega), ← List.dropLast_eq_take]
  exact List.mem_of_mem_dropLast (kept ▸ older)

/-- The caller's post-fetch continuation and live prefix form the saved frame
needed for entry. The argument words remain available to the new callee. -/
theorem prepare_saved_caller {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled functions targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes functions)
    (point : StructuredFramePoint raw source compiled functions targets next output)
    (index : Usize) (pc : U32) (lookup : exec.frames.val[index.val]? = some raw)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Code.slots ((source.locals ++ front).map Code.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Code.CodeRel source.module.TYPES functions source.resultTypes
      (source.locals.map Code.valueType) compiled.code.val targets
      (front.map Code.valueType ++ returns) after pc.val next output) :
    SavedFrame store { exec with frames := exec.frames.set index { raw with pc := pc } }
      { raw with pc := pc } { source with vals := front, code := after } returns base := by
  refine ⟨binding.advance index pc lookup, ?_, destination,
    compiled, functions, targets, next, output, ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩,
    point.suspend front args after pc returns split heights continuation⟩
  apply WordsAt.append_left (right := Code.encodeValues args)
  simpa only [FrameSlots, ValuesAt, split, Code.encodeValues_append, List.append_assoc] using slots

/-- After successful entry, the initialized callee and prepared caller chain
constitute the complete frame-stack relation. -/
theorem FrameStackRel.call_enter {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {raws : List runtime.interp.Frame} {sources : List Abs.AFrame}
    {instanceIndex functionIndex base : Usize} {compiled : runtime.bytecode.CompiledFunction}
    (effect : CallEntryEffect before after instanceIndex functionIndex base compiled)
    (source : Abs.AFrame)
    (frames : before.frames.val = raws.reverse)
    (saved : SavedFrames store before raws sources source.resultTypes base.val)
    (active : ActiveFrame store after ⟨instanceIndex, functionIndex, 0#u32, base⟩ source)
    (params : compiled.param_slots.val ≤ compiled.local_slots.val)
    (capacity : compiled.local_slots.val ≤ compiled.slot_count.val) :
    FrameStackRel store after (source :: sources) := by
  exact .active (by rw [effect.1, frames]) active
    (saved.call_preserved effect (Nat.le_refl _) params capacity)

end Exec.Interp
