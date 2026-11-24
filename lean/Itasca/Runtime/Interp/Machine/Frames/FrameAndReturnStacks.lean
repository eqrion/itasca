import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Calls.ReturnRefinement

/-!
Proofs for Runtime / Interp / Machine / Frames.

This module collects FrameStack, ReturnStack.
Each section documents its contracts and consumers.
-/

/-! ## FrameStack -/

section

open Itasca.Representation

/-!
Saved and active frames in the structured machine relation.

Main declarations: `FrameStackRel` and `SavedFrames`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

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
    {oldSource newSource : _root_.store} (metadata : Store.MetadataPreserved before after)
    (extension : Extend_store oldSource newSource) {exec raw source waiting childBase}
    (saved : SavedFrame before oldSource exec raw source waiting childBase) :
    SavedFrame after newSource exec raw source waiting childBase := by
  refine ⟨saved.binding.store_metadata metadata,saved.slots,saved.destination,?_⟩
  obtain ⟨compiled,C,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,C,targets,next,output,program.store_metadata metadata,point.extend extension⟩

theorem SavedFrames.store_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (metadata : Store.MetadataPreserved before after)
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
        preserve _ _ head.slots (by rw [Representation.encode_values_length,←head.destination]),head.destination,head.continuation⟩
    · apply ih
      · intro other source binding member
        exact bindings other source binding (by simp only [List.mem_cons]; exact Or.inr member)
      · intro position bits represented bound
        exact preserve position bits represented (bound.trans head.base_le)

def ReadyTop {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (source : SourceMachine.AFrame) : Prop :=
  ∃ raw compiled C targets next output,
    exec.frames.val.getLast? = some raw ∧
    FrameProgram store raw compiled (source.locals.map Representation.valueType) source.resultTypes C.FUNCS ∧
    FramePoint sourceStore raw source compiled C targets next output

theorem ActiveFrame.store_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (metadata : Store.MetadataPreserved before after)
    (extension : Extend_store oldSource newSource) {exec raw source}
    (active : ActiveFrame before oldSource exec raw source) : ActiveFrame after newSource exec raw source := by
  refine ⟨active.binding.store_metadata metadata,active.slots,?_⟩
  obtain ⟨compiled,C,targets,next,output,pending,program,point⟩ := active.continuation
  exact ⟨compiled,C,targets,next,output,pending,program.store_metadata metadata,point.extend extension⟩

theorem FrameStackRel.store_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (metadata : Store.MetadataPreserved before after)
    (extension : Extend_store oldSource newSource) {exec sources}
    (stack : FrameStackRel before oldSource exec sources) : FrameStackRel after newSource exec sources := by
  cases stack with
  | empty frames => exact .empty frames
  | active frames top saved => exact .active frames (top.store_extension metadata extension) (saved.store_extension metadata extension)

def ReadyState {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution) (source : SourceMachine.AState) : Prop :=
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
    (types : results.map Representation.valueType = waiting) (width : count = Representation.slots (results.map Representation.valueType))
    (bounds : base + src + count ≤ before.slots.length) (heights : SourceMachine.FrameHeights source) :
    FrameBinding store after raw {source with vals := source.vals ++ results} ∧
    FrameSlots after raw {source with vals := source.vals ++ results} ∧
    ∃ compiled C targets next output,
      FrameProgram store raw compiled (source.locals.map Representation.valueType) source.resultTypes C.FUNCS ∧
      FramePoint sourceStore raw {source with vals := source.vals ++ results} compiled C targets next output := by
  refine ⟨effect.preserve_binding saved.binding member,
    effect.resume saved.slots represented width saved.destination bounds,?_⟩
  obtain ⟨compiled,C,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,C,targets,next,output,program,point.resume results types heights⟩

end Itasca.Interp.Machine

end

/-! ## ReturnStack -/

section

/-!
Proofs for Runtime / Interp / Machine / Frames.

This module collects StackPreservation, ReturnStack.
Each section documents its contracts and consumers.
-/

/-! ## StackPreservation -/

section

/-!
A checked ordinary mutation preserves the full caller chain through both source store extension and exact concrete metadata/prefix preservation.

Main declarations: `FrameStackRel.step_active` and `FrameStackRel.single_base`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

/-- A checked ordinary mutation preserves the full caller chain through both
source store extension and exact concrete metadata/prefix preservation. -/
theorem FrameStackRel.step_active {M : Type} {oldStore newStore : runtime.store.Store M}
    {oldSourceStore newSourceStore : _root_.store}
    {before after : runtime.interp.Execution} {source updatedSource : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (relation : FrameStackRel oldStore oldSourceStore before (source :: rest))
    (metadata : Store.MetadataPreserved oldStore newStore) (extension : Extend_store oldSourceStore newSourceStore)
    (raw updated : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    (frames : after.frames.val = before.frames.val.dropLast ++ [updated])
    (sameBase : updated.base = raw.base) (sameReturns : updatedSource.resultTypes = source.resultTypes)
    (identity : after.store = before.store) (capacity : before.slots.length ≤ after.slots.length)
    (preserve : ∀ position bits, WordsAt before.slots.val position bits →
      position + bits.length ≤ raw.base.val → WordsAt after.slots.val position bits)
    (active : ActiveFrame newStore newSourceStore after updated updatedSource) :
    FrameStackRel newStore newSourceStore after (updatedSource :: rest) := by
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
    {exec : runtime.interp.Execution} {source : SourceMachine.AFrame}
    (relation : FrameStackRel store sourceStore exec [source])
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw) : raw.base.val = 0 := by
  cases relation with
  | @active actual _ raws _ frames active saved =>
    have same : actual = raw := by simpa only [frames,List.getLast?_concat,Option.some.injEq] using top
    subst actual
    exact saved.empty_inv.2

end Itasca.Interp.Machine

end

/-! ## ReturnStack -/

section

open Itasca.Representation

/-!
Returning to a suspended caller restores the active certificate and preserves the older caller chain.

Main declarations: `FrameStackRel.return_to_caller_ready` and `FrameStackRel.return_complete`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

/-- Returning to a suspended caller restores the active certificate and
preserves the older caller chain. -/
theorem FrameStackRel.return_to_caller_ready {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {callee caller : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (relation : FrameStackRel store sourceStore before (callee :: caller :: rest))
    (raw : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    {src count : Nat} (effect : ReturnEffect before after raw.base.val src count)
    (results : List val)
    (represented : ValuesAt before.slots.val (raw.base.val + src) results)
    (types : results.map Representation.valueType = callee.resultTypes)
    (width : count = Representation.slots (results.map Representation.valueType))
    (bounds : raw.base.val + src + count ≤ before.slots.length)
    (heights : SourceMachine.FrameHeights caller) :
    FrameStackRel store sourceStore after ({ caller with vals := caller.vals ++ results } :: rest) ∧
      ReadyTop store sourceStore after { caller with vals := caller.vals ++ results } := by
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
      obtain ⟨binding, slots, compiled, C, targets, next, output, program, point⟩ :=
        head.resume effect member results represented types width bounds heights
      constructor
      · apply FrameStackRel.active
        · simpa only [List.reverse_cons] using effect.frames frames
        · exact ⟨binding, slots, compiled, C, targets, next, output, false, program, .ready point⟩
        · apply tail.return_preserved effect head.base_le _ bounds
          intro frame found
          rw [remaining]
          exact List.mem_append_left _ (List.mem_reverse.mpr found)
      · refine ⟨callerRaw, compiled, C, targets, next, output, ?_, program, point⟩
        rw [effect.frames frames]
        simp

/-- The last return removes the concrete frame stack completely. -/
theorem FrameStackRel.return_final {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {callee : SourceMachine.AFrame}
    (relation : FrameStackRel store sourceStore before [callee])
    {base src count : Nat} (effect : ReturnEffect before after base src count) :
    FrameStackRel store sourceStore after [] := by
  cases relation with
  | active frames active saved =>
    obtain ⟨empty, _⟩ := saved.empty_inv
    apply FrameStackRel.empty
    simpa only [empty, List.reverse_nil] using effect.frames frames

theorem FrameStackRel.return_complete {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {callee : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (relation : FrameStackRel store sourceStore before (callee :: rest))
    (ambient : frame)
    (raw : runtime.interp.Frame) (top : before.frames.val.getLast? = some raw)
    {src count : Nat} (effect : ReturnEffect before after raw.base.val src count)
    (results : List val)
    (represented : ValuesAt before.slots.val (raw.base.val + src) results)
    (types : results.map Representation.valueType = callee.resultTypes)
    (width : count = Representation.slots (results.map Representation.valueType))
    (bounds : raw.base.val + src + count ≤ before.slots.length)
    (heights : ∀ caller ∈ rest, SourceMachine.FrameHeights caller) :
    FrameStackRel store sourceStore after (returnedState sourceStore ambient rest results).frames ∧
      ReadyState store after (returnedState sourceStore ambient rest results) := by
  cases rest with
  | nil =>
    refine ⟨relation.return_final effect, ?_⟩
    have base := relation.single_base raw top
    simpa only [ReadyState, returnedState, base] using effect.results represented width bounds
  | cons caller rest =>
    exact relation.return_to_caller_ready raw top effect results represented types width bounds
      (heights caller (by simp))

end Itasca.Interp.Machine

end

end
