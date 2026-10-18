import Exec.Representation.FunctionTable
import Exec.Interp.Relations.SuspendedPoint
import Exec.Interp.Calls.ReturnRegions
import Exec.Interp.Calls.CallFrames

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Code safety and exact retained store lookups for a concrete frame. -/
structure FrameProgram {M : Type} (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (locals results : List valtype) (functions : List functype) : Prop where
  lookup : ∃ inst, store.instances.val[raw.instance.val]? = some inst ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    FunctionTable store inst functions
  checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true
  fetchBound : compiled.code.val.length ≤ U32.max
  localSlots : compiled.local_slots.val = Code.slots locals
  epilogue : ∃ pc count : U32, compiled.code.val.length = pc.val + 1 ∧
    compiled.code.val[pc.val]? = some (.Return compiled.local_slots count)

/-- A caller retains its live data and the typed code continuation awaiting
its child's results. The child's base is exactly the end of that live data. -/
structure SavedFrame {M : Type} (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : Abs.AFrame) (waiting : List valtype) (childBase : Nat) : Prop where
  binding : FrameBinding store exec raw source
  slots : FrameSlots exec raw source
  destination : childBase = raw.base.val + Code.slots ((source.locals ++ source.vals).map Code.valueType)
  continuation : ∃ compiled functions targets next output,
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes functions ∧
    SuspendedFramePoint raw source compiled functions targets next output waiting

/-- Suspended callers are ordered innermost first, matching the abstract
machine. Concrete frame vectors use the reverse of this order. The outermost frame
starts at slot zero, where invocation result readback begins. -/
inductive SavedFrames {M : Type} (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) :
    List runtime.interp.Frame → List Abs.AFrame → List valtype → Nat → Prop where
  | nil (waiting) : SavedFrames store exec [] [] waiting 0
  | cons {raw raws source sources waiting base} :
      SavedFrame store exec raw source waiting base →
      SavedFrames store exec raws sources source.resultTypes raw.base.val →
      SavedFrames store exec (raw :: raws) (source :: sources) waiting base

/-- An empty suspended chain identifies both the empty concrete prefix and
the zero base of the outermost invocation frame. -/
theorem SavedFrames.empty_inv {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raws waiting base}
    (saved : SavedFrames store exec raws [] waiting base) : raws = [] ∧ base = 0 := by
  cases saved
  exact ⟨rfl, rfl⟩

/-- Every saved caller region lies below its direct child's base. -/
theorem SavedFrame.base_le {M : Type} {store : runtime.store.Store M}
    {exec raw source waiting childBase}
    (saved : SavedFrame store exec raw source waiting childBase) : raw.base.val ≤ childBase := by
  rw [saved.destination]
  omega

/-- A storage change that preserves bindings and the prefix below the active
callee preserves the entire suspended stack, including its code certificates. -/
theorem SavedFrames.transport {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {raws sources waiting base}
    (saved : SavedFrames store before raws sources waiting base)
    (bindings : ∀ raw source, FrameBinding store before raw source →
      raw ∈ raws → FrameBinding store after raw source)
    (preserve : ∀ position bits, WordsAt before.slots.val position bits →
      position + bits.length ≤ base → WordsAt after.slots.val position bits) :
    SavedFrames store after raws sources waiting base := by
  induction saved with
  | nil => exact .nil _
  | @cons raw raws source sources waiting base head tail ih =>
    apply SavedFrames.cons
    · exact ⟨bindings raw source head.binding (by simp),
        preserve _ _ head.slots (by rw [Code.encodeValues_length, ← head.destination]),
        head.destination, head.continuation⟩
    · apply ih
      · intro other source binding member
        exact bindings other source binding (by simp only [List.mem_cons]; exact Or.inr member)
      · intro position bits represented below
        exact preserve position bits represented (below.trans head.base_le)

/-- Entering a deeper callee preserves the suspended chain below the active
frame, including allocation growth and local initialization. -/
theorem SavedFrames.call_preserved {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {raws sources waiting boundary}
    (saved : SavedFrames store before raws sources waiting boundary)
    {instanceIndex functionIndex base : Usize} {compiled : runtime.bytecode.CompiledFunction}
    (effect : CallEntryEffect before after instanceIndex functionIndex base compiled)
    (below : boundary ≤ base.val)
    (params : compiled.param_slots.val ≤ compiled.local_slots.val)
    (capacity : compiled.local_slots.val ≤ compiled.slot_count.val) :
    SavedFrames store after raws sources waiting boundary := by
  apply saved.transport
  · intro raw source binding _
    exact effect.preserve_binding binding
  · intro position bits represented bound
    exact effect.preserve_prefix represented (bound.trans below) params capacity

/-- Popping the active callee preserves every older caller below a retained
boundary. The immediate caller is resumed separately with the copied results. -/
theorem SavedFrames.return_preserved {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {raws sources waiting boundary}
    (saved : SavedFrames store before raws sources waiting boundary)
    {base src count : Nat} (effect : ReturnEffect before after base src count)
    (below : boundary ≤ base)
    (members : ∀ raw ∈ raws, raw ∈ before.frames.val.dropLast)
    (bounds : base + src + count ≤ before.slots.length) :
    SavedFrames store after raws sources waiting boundary := by
  apply saved.transport
  · intro raw source binding member
    exact effect.preserve_binding binding (members raw member)
  · intro position bits represented bound
    exact effect.preserve_prefix represented (bound.trans below) bounds

/-- Returning restores both the represented caller values and its retained
structured continuation. -/
theorem SavedFrame.resume {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {raw source waiting base src count}
    (saved : SavedFrame store before raw source waiting base)
    (effect : ReturnEffect before after base src count)
    (member : raw ∈ before.frames.val.dropLast)
    (results : List val) (represented : ValuesAt before.slots.val (base + src) results)
    (types : results.map Code.valueType = waiting)
    (width : count = Code.slots (results.map Code.valueType))
    (bounds : base + src + count ≤ before.slots.length)
    (heights : Abs.FrameHeights source) :
    FrameBinding store after raw { source with vals := source.vals ++ results } ∧
    FrameSlots after raw { source with vals := source.vals ++ results } ∧
    ∃ compiled functions targets next output,
      FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes functions ∧
      StructuredFramePoint raw { source with vals := source.vals ++ results }
        compiled functions targets next output := by
  refine ⟨effect.preserve_binding saved.binding member,
    effect.resume saved.slots represented width saved.destination bounds, ?_⟩
  obtain ⟨compiled, functions, targets, next, output, program, point⟩ := saved.continuation
  exact ⟨compiled, functions, targets, next, output, program, point.resume results types heights⟩

end Exec.Interp
