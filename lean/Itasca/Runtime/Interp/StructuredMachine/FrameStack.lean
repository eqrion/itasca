import Itasca.Runtime.Interp.StructuredMachine.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

structure SavedFrame {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : Abs.AFrame) (waiting : List valtype) (childBase : Nat) : Prop where
  binding : FrameBinding store exec raw source
  slots : FrameSlots exec raw source
  destination : childBase = raw.base.val + Code.slots ((source.locals ++ source.vals).map Code.valueType)
  continuation : ∃ compiled C targets next output,
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS ∧
    SuspendedFramePoint sourceStore raw source compiled C targets next output waiting

inductive SavedFrames {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) :
    List runtime.interp.Frame → List Abs.AFrame → List valtype → Nat → Prop where
  | nil (waiting) : SavedFrames store sourceStore exec [] [] waiting 0
  | cons {raw raws source sources waiting base} :
      SavedFrame store sourceStore exec raw source waiting base →
      SavedFrames store sourceStore exec raws sources source.resultTypes raw.base.val →
      SavedFrames store sourceStore exec (raw :: raws) (source :: sources) waiting base

theorem SavedFrames.empty_inv {M : Type} {store : runtime.store.Store M} {sourceStore exec raws waiting base}
    (saved : SavedFrames store sourceStore exec raws [] waiting base) : raws = [] ∧ base = 0 := by
  cases saved
  exact ⟨rfl,rfl⟩

theorem SavedFrame.base_le {M : Type} {store : runtime.store.Store M} {sourceStore exec raw source waiting childBase}
    (saved : SavedFrame store sourceStore exec raw source waiting childBase) : raw.base.val ≤ childBase := by
  rw [saved.destination]
  omega

/-- Concrete metadata and generated source extension jointly transport all
suspended contexts through memory/global content mutations. -/
theorem SavedFrame.store_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (metadata : FrameStoreMetadata before after)
    (extension : Extend_store oldSource newSource) {exec raw source waiting childBase}
    (saved : SavedFrame before oldSource exec raw source waiting childBase) :
    SavedFrame after newSource exec raw source waiting childBase := by
  refine ⟨saved.binding.store_metadata metadata,saved.slots,saved.destination,?_⟩
  obtain ⟨compiled,C,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,C,targets,next,output,program.store_metadata metadata,point.extend extension⟩

theorem SavedFrames.store_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (metadata : FrameStoreMetadata before after)
    (extension : Extend_store oldSource newSource) {exec raws sources waiting base}
    (saved : SavedFrames before oldSource exec raws sources waiting base) :
    SavedFrames after newSource exec raws sources waiting base := by
  induction saved with
  | nil waiting => exact .nil waiting
  | cons head tail ih => exact .cons (head.store_extension metadata extension) ih

theorem SavedFrames.transport {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {raws sources waiting base}
    (saved : SavedFrames store sourceStore before raws sources waiting base)
    (bindings : ∀ raw source, FrameBinding store before raw source → raw ∈ raws → FrameBinding store after raw source)
    (preserve : ∀ position bits, WordsAt before.slots.val position bits →
      position + bits.length ≤ base → WordsAt after.slots.val position bits) :
    SavedFrames store sourceStore after raws sources waiting base := by
  induction saved with
  | nil => exact .nil _
  | @cons raw raws source sources waiting base head tail ih =>
    apply SavedFrames.cons
    · exact ⟨bindings raw source head.binding (by simp),
        preserve _ _ head.slots (by rw [Code.encodeValues_length,←head.destination]),head.destination,head.continuation⟩
    · apply ih
      · intro other source binding member
        exact bindings other source binding (by simp only [List.mem_cons]; exact Or.inr member)
      · intro position bits represented bound
        exact preserve position bits represented (bound.trans head.base_le)

structure ActiveFrame {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (source : Abs.AFrame) : Prop where
  binding : FrameBinding store exec raw source
  slots : FrameSlots exec raw source
  continuation : ∃ compiled C targets next output pending,
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS ∧
    ControlPoint sourceStore raw source compiled C targets next output pending

def ReadyTop {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (source : Abs.AFrame) : Prop :=
  ∃ raw compiled C targets next output,
    exec.frames.val.getLast? = some raw ∧
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS ∧
    FramePoint sourceStore raw source compiled C targets next output

inductive FrameStackRel {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) : List Abs.AFrame → Prop where
  | empty (frames : exec.frames.val = []) : FrameStackRel store sourceStore exec []
  | active {raw source raws sources}
      (frames : exec.frames.val = raws.reverse ++ [raw])
      (top : ActiveFrame store sourceStore exec raw source)
      (saved : SavedFrames store sourceStore exec raws sources source.resultTypes raw.base.val) :
      FrameStackRel store sourceStore exec (source :: sources)

theorem ActiveFrame.store_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (metadata : FrameStoreMetadata before after)
    (extension : Extend_store oldSource newSource) {exec raw source}
    (active : ActiveFrame before oldSource exec raw source) : ActiveFrame after newSource exec raw source := by
  refine ⟨active.binding.store_metadata metadata,active.slots,?_⟩
  obtain ⟨compiled,C,targets,next,output,pending,program,point⟩ := active.continuation
  exact ⟨compiled,C,targets,next,output,pending,program.store_metadata metadata,point.extend extension⟩

theorem FrameStackRel.store_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (metadata : FrameStoreMetadata before after)
    (extension : Extend_store oldSource newSource) {exec sources}
    (stack : FrameStackRel before oldSource exec sources) : FrameStackRel after newSource exec sources := by
  cases stack with
  | empty frames => exact .empty frames
  | active frames top saved => exact .active frames (top.store_extension metadata extension) (saved.store_extension metadata extension)

def ReadyState {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution) (source : Abs.AState) : Prop :=
  match source.frames with
  | [] => ValuesAt exec.slots.val 0 source.results
  | frame :: _ => ReadyTop store source.store exec frame
theorem SavedFrames.call_preserved {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {raws sources waiting boundary}
    (saved : SavedFrames store sourceStore before raws sources waiting boundary)
    {instanceIndex functionIndex base : Usize} {compiled : runtime.bytecode.CompiledFunction}
    (effect : CallEntryEffect before after instanceIndex functionIndex base compiled)
    (below : boundary ≤ base.val) (params : compiled.param_slots.val ≤ compiled.local_slots.val)
    (capacity : compiled.local_slots.val ≤ compiled.slot_count.val) :
    SavedFrames store sourceStore after raws sources waiting boundary := by
  apply saved.transport
  · intro raw source binding _
    exact effect.preserve_binding binding
  · intro position bits represented bound
    exact effect.preserve_prefix represented (bound.trans below) params capacity

theorem SavedFrames.return_preserved {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {raws sources waiting boundary}
    (saved : SavedFrames store sourceStore before raws sources waiting boundary)
    {base src count : Nat} (effect : ReturnEffect before after base src count)
    (below : boundary ≤ base) (members : ∀ raw ∈ raws, raw ∈ before.frames.val.dropLast)
    (bounds : base + src + count ≤ before.slots.length) :
    SavedFrames store sourceStore after raws sources waiting boundary := by
  apply saved.transport
  · intro raw source binding member
    exact effect.preserve_binding binding (members raw member)
  · intro position bits represented bound
    exact effect.preserve_prefix represented (bound.trans below) bounds

theorem SavedFrame.resume {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {raw source waiting base src count}
    (saved : SavedFrame store sourceStore before raw source waiting base)
    (effect : ReturnEffect before after base src count) (member : raw ∈ before.frames.val.dropLast)
    (results : List val) (represented : ValuesAt before.slots.val (base + src) results)
    (types : results.map Code.valueType = waiting) (width : count = Code.slots (results.map Code.valueType))
    (bounds : base + src + count ≤ before.slots.length) (heights : Abs.FrameHeights source) :
    FrameBinding store after raw {source with vals := source.vals ++ results} ∧
    FrameSlots after raw {source with vals := source.vals ++ results} ∧
    ∃ compiled C targets next output,
      FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS ∧
      FramePoint sourceStore raw {source with vals := source.vals ++ results} compiled C targets next output := by
  refine ⟨effect.preserve_binding saved.binding member,
    effect.resume saved.slots represented width saved.destination bounds,?_⟩
  obtain ⟨compiled,C,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,C,targets,next,output,program,point.resume results types heights⟩

end Itasca.Runtime.Interp.StructuredMachine
