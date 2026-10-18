import Exec.Interp.Relations.FrameStack
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Calls.ReturnRefinement

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The active frame combines allocated data, exact code lookup, and either
an ordinary structured position or the pending jump after a branch copy. -/
structure ActiveFrame {M : Type} (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (source : Abs.AFrame) : Prop where
  binding : FrameBinding store exec raw source
  slots : FrameSlots exec raw source
  continuation : ∃ compiled functions targets next output pending,
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes functions ∧
    ControlPoint raw source compiled functions targets next output pending

/-- A ready continuation tied to the actual last frame, with no pending
second half of an emitted branch. -/
def ReadyTop {M : Type} (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (source : Abs.AFrame) : Prop :=
  ∃ raw compiled functions targets next output,
    exec.frames.val.getLast? = some raw ∧
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes functions ∧
    StructuredFramePoint raw source compiled functions targets next output

/-- Concrete frame vectors grow at the end; source frames are innermost first.
Every suspended frame records the live region below its child's base. -/
inductive FrameStackRel {M : Type} (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) : List Abs.AFrame → Prop where
  | empty (frames : exec.frames.val = []) : FrameStackRel store exec []
  | active {raw source raws sources}
      (frames : exec.frames.val = raws.reverse ++ [raw])
      (top : ActiveFrame store exec raw source)
      (saved : SavedFrames store exec raws sources source.resultTypes raw.base.val) :
      FrameStackRel store exec (source :: sources)

/-- The compiler's code-length certificate rules out PC increment overflow
whenever the interpreter fetches an actual instruction. -/
theorem FrameProgram.fetched_bound {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions} (program : FrameProgram store raw compiled locals results functions)
    (instruction : runtime.bytecode.Instr)
    (fetched : compiled.code.val[raw.pc.val]? = some instruction) : raw.pc.val < U32.max := by
  have bound := (List.getElem?_eq_some_iff.mp fetched).1
  exact lt_of_lt_of_le bound program.fetchBound

/-- Returning to a suspended caller restores the active certificate and
preserves the older caller chain. -/
theorem FrameStackRel.return_to_caller_ready {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {callee caller : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store before (callee :: caller :: rest))
    (raw : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    {src count : Nat} (effect : ReturnEffect before after raw.base.val src count)
    (results : List val)
    (represented : ValuesAt before.slots.val (raw.base.val + src) results)
    (types : results.map Code.valueType = callee.resultTypes)
    (width : count = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val + src + count ≤ before.slots.length)
    (heights : Abs.FrameHeights caller) :
    FrameStackRel store after ({ caller with vals := caller.vals ++ results } :: rest) ∧
      ReadyTop store after { caller with vals := caller.vals ++ results } := by
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
      obtain ⟨binding, slots, compiled, functions, targets, next, output, program, point⟩ :=
        head.resume effect member results represented types width bounds heights
      constructor
      · apply FrameStackRel.active
        · simpa only [List.reverse_cons] using effect.frames frames
        · exact ⟨binding, slots, compiled, functions, targets, next, output, false, program, .ready point⟩
        · apply tail.return_preserved effect head.base_le _ bounds
          intro frame found
          rw [remaining]
          exact List.mem_append_left _ (List.mem_reverse.mpr found)
      · refine ⟨callerRaw, compiled, functions, targets, next, output, ?_, program, point⟩
        rw [effect.frames frames]
        simp

theorem FrameStackRel.return_to_caller {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {callee caller : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store before (callee :: caller :: rest))
    (raw : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    {src count : Nat} (effect : ReturnEffect before after raw.base.val src count)
    (results : List val)
    (represented : ValuesAt before.slots.val (raw.base.val + src) results)
    (types : results.map Code.valueType = callee.resultTypes)
    (width : count = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val + src + count ≤ before.slots.length)
    (heights : Abs.FrameHeights caller) :
    FrameStackRel store after ({ caller with vals := caller.vals ++ results } :: rest) := by
  exact (relation.return_to_caller_ready raw top effect results represented types width bounds heights).1

/-- The final active frame starts where public invocation result readback
begins: slot zero. This follows from the suspended-chain boundary. -/
theorem FrameStackRel.single_base {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AFrame}
    (relation : FrameStackRel store exec [source])
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw) : raw.base.val = 0 := by
  cases relation with
  | @active actual _ raws _ frames active saved =>
    have same : actual = raw := by simpa only [frames, List.getLast?_concat, Option.some.injEq] using top
    subst actual
    exact saved.empty_inv.2

/-- The last return removes the concrete frame stack completely. -/
theorem FrameStackRel.return_final {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {callee : Abs.AFrame}
    (relation : FrameStackRel store before [callee])
    {base src count : Nat} (effect : ReturnEffect before after base src count) :
    FrameStackRel store after [] := by
  cases relation with
  | active frames active saved =>
    obtain ⟨empty, _⟩ := saved.empty_inv
    apply FrameStackRel.empty
    simpa only [empty, List.reverse_nil] using effect.frames frames

/-- A completed return retains either its resumed ready continuation or the
final results at the public readback origin. -/
def ReadyState {M : Type} (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (source : Abs.AState) : Prop :=
  match source.frames with
  | [] => ValuesAt exec.slots.val 0 source.results
  | f :: _ => ReadyTop store exec f

theorem FrameStackRel.return_complete {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {callee : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store before (callee :: rest))
    (s : _root_.store) (ambient : frame)
    (raw : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    {src count : Nat} (effect : ReturnEffect before after raw.base.val src count)
    (results : List val)
    (represented : ValuesAt before.slots.val (raw.base.val + src) results)
    (types : results.map Code.valueType = callee.resultTypes)
    (width : count = Code.slots (results.map Code.valueType))
    (bounds : raw.base.val + src + count ≤ before.slots.length)
    (heights : ∀ caller ∈ rest, Abs.FrameHeights caller) :
    FrameStackRel store after (returnedState s ambient rest results).frames ∧
      ReadyState store after (returnedState s ambient rest results) := by
  cases rest with
  | nil =>
    refine ⟨relation.return_final effect, ?_⟩
    have base := relation.single_base raw top
    simpa only [ReadyState, returnedState, base] using effect.results represented width bounds
  | cons caller rest =>
    exact relation.return_to_caller_ready raw top effect results represented types width bounds
      (heights caller (by simp))

end Exec.Interp
