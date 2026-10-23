import Exec.Interp.StructuredMachine.CallStack
import Exec.Interp.Control.SkipStack

namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- Fetch advances the caller PC and removes argument values from its saved
live prefix, preparing the complete suspended chain for a defined call. -/
theorem FrameStackRel.prepare_call {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store s exec (source :: rest))
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw source compiled C targets next output)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Code.slots ((source.locals ++ front).map Code.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Code.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Code.valueType ++ returns) after pc.val next output) :
    ∃ raws,
      (exec.frames.set index { raw with pc := pc }).val = raws.reverse ∧
      SavedFrames store s { exec with frames := exec.frames.set index { raw with pc := pc } }
        raws ({ source with vals := front, code := after } :: rest) returns base := by
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length - 1 = index.val := by change exec.frames.length - 1 = index.val; omega
    rw [position]
    exact lookup
  cases relation with
  | @active actual _ raws _ frames active saved =>
    have same : actual = raw := by simpa only [frames, List.getLast?_concat, Option.some.injEq] using top
    subst actual
    have remaining : exec.frames.val.dropLast = raws.reverse := by rw [frames, List.dropLast_concat]
    refine ⟨{ raw with pc := pc } :: raws, ?_, ?_⟩
    · rw [frames_set_last exec index _ last, remaining, List.reverse_cons]
    · apply SavedFrames.cons
      · exact prepare_saved_caller binding slots program point index pc lookup front args after returns base
          split destination heights continuation
      · apply saved.transport
        · intro frame source binding member
          exact binding.advance_older index { raw with pc := pc } last (by rw [remaining]; exact List.mem_reverse.mpr member)
        · intro position bits represented _
          exact represented

end Exec.Interp.StructuredMachine
