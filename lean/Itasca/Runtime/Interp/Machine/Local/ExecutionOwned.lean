import Itasca.Runtime.Interp.Machine.Normalization.IndexedLinear
import Itasca.Runtime.Interp.Machine.Local.Inversion
import Itasca.Runtime.Interp.Relations.LocalCapacity
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Interp.Machine.Retention.Ownership
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Normalization.LinearContinuation
import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Relations.LocalCodePoint
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Machine.Local.MovePrefix
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Interp.Machine.Control.UniformSource
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.Spec.Extend

/-!
Local-variable structured execution and ownership. Fetch, capacity and get/write frame effects assemble the complete execution relation without changing surrounding frame slots.
-/

/-! ## Local Capacity -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp.StructuredMachine
/-- Even behind forward skips, a local read's destination lies within the
allocation checked for the complete function bytecode. -/
theorem structured_local_get_capacity
    (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype)
    (labels : List LabelTarget) (index : Nat) (after : List instr)
    (next : Nat) (output : List valtype) (ty : valtype)
    (localType : C.LOCALS[index]? = some ty) :
    ∀ pc, StructuredCode (Interp.emission compiled C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.LOCAL_GET (.mk_uN index) :: after) pc next output →
      slots C.LOCALS + slots stack + width ty ≤ compiled.slot_count.val := by
  intro pc relation
  generalize measureEq : compiled.code.val.length - pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases Interp.StructuredMachine.structuredCode_linear_inv (by rfl) relation with skip | branch
    · obtain ⟨target, forward, fetched, continuation⟩ := skip
      have targetBound := continuation.entry_bound
      exact ih (compiled.code.val.length - target.val) (by omega) target.val continuation rfl
    · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
      obtain ⟨actual, src, dst, actualType, emittedEq, middleEq, source, position⟩ :=
        Interp.linearEmission_localGet_inv index (Interp.StructuredMachine.emission_localGet_pure index head)
      have same : actual = ty := Option.some.inj (actualType.symm.trans localType)
      subst actual
      have fetched : compiled.code.val[pc]? = some (move ty dst src) := by
        simpa only [Nat.add_zero] using fragment.fetch (index := 0)
          (by simp only [emittedEq, List.getElem?_cons_zero])
      have valid := well_formed_fetched compiled checked pc _ fetched
      have bound := (move_valid_bounds compiled ty dst src valid).1
      simpa only [position] using bound

end Itasca.Runtime.Code

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp.StructuredMachine
/-- LOCAL_GET needs no independent spare-capacity premise: retained code and
frame certificates establish it for the actual represented local value. -/
theorem structured_local_get_storage_capacity {M : Type}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    {s C targets next output} (index : Nat) (after : List instr)
    (point : FramePoint s raw { source with code := .LOCAL_GET (.mk_uN index) :: after }
      compiled C targets next output)
    (value : val) (lookup : source.locals[index]? = some value) :
    raw.base.val + Code.slots ((source.locals ++ source.vals).map Code.valueType) +
      Code.width (Code.valueType value) ≤ exec.slots.length := by
  have localType : (source.locals.map Code.valueType)[index]? = some (Code.valueType value) := by
    simp only [List.getElem?_map, lookup, Option.map_some]
  have bound := Code.structured_local_get_capacity compiled checked C source.resultTypes
    (source.vals.map Code.valueType) targets index after next output
    (Code.valueType value) (by simpa only [point.locals] using localType) raw.pc.val point.code.current
  rw [point.locals] at bound
  change Code.slots (source.locals.map Code.valueType) + Code.slots (source.vals.map Code.valueType) + Code.width (Code.valueType value) ≤ compiled.slot_count.val at bound
  have capacity := binding.capacity inst compiled hi hc
  simp only [List.map_append, Code.slots_append]
  omega

end Itasca.Runtime.Interp

end

/-! ## Local Get Owned -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std
theorem step_localGet_owned_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (localIndex : U32) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.CoreTyped ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : ∀ value, f.locals[localIndex.val]? = some value →
      raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) + Code.width (Code.valueType value) ≤ exec.slots.length)
    (point : FramePoint s raw { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (targets' : List Code.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool), raw.pc.val < pc.val ∧ pending = false ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        Abs.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        (g = {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} ∨ ∃locals values, g = {f with code := after,locals := locals,vals := values}) ∧
        FrameOwnershipClosure {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} g ⦄ := by
  rcases structuredCode_linear_inv (by rfl) point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after },
      targets, next, output, false, forward, rfl, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨ty, src, dst, localType, emittedEq, middleEq, source, position⟩ := linearEmission_localGet_inv localIndex.val (emission_localGet_pure localIndex.val head)
    obtain ⟨value, lookup, tyEq⟩ := values_type_lookup f.locals localIndex.val ty (by simpa only [point.locals] using localType)
    subst ty
    have destination : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType) := by
      simpa only [point.locals,List.map_append, Code.slots_append] using position
    have fetched : compiled.code.val[raw.pc.val]? = some (Code.move (Code.valueType value) dst src) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have frameTyped : Abs.FrameTyped s { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    have localBound : localIndex.val < f.locals.length := List.getElem?_eq_some_iff.mp lookup |>.1
    have valueEq : f.locals[localIndex.val]! = value := by
      simpa only [List.getElem?_eq_getElem localBound, Option.some.injEq, getElem!_pos f.locals localIndex.val localBound] using lookup
    have nextFrame := Abs.local_get_frame_preservation frameTyped
    rw [valueEq] at nextFrame
    have nextTyped := Abs.active_frame_preservation typed.typed nextFrame rfl
    have labelsAfter : LabelsMatch (f.vals ++ [value]) f.labels targets := by
      have old : LabelsMatch (f.vals ++ []) f.labels targets := by simpa only [List.append_nil] using point.labels
      have heights := Abs.frameTyped_heights frameTyped
      exact old.replace_suffix heights
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Code.move (Code.valueType value) dst src) last hf hi hc fetched pcBound
    intro pc hpc
    have nextPoint : FramePoint s { raw with pc := pc }
        { f with code := after, vals := f.vals ++ [value] }
        compiled C targets next output := by
      apply linear_continuation point pc f.locals (f.vals ++ [value]) after middle
      · simpa only [endpoint, hpc] using continuation
      · rfl
      · simp only [middleEq, List.map_append, List.map_cons, List.map_nil]
      · exact labelsAfter
    apply WP.spec_mono (dispatch_localGet_refines memory hooks floats allocator
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index raw localIndex src dst
      s ambient f rest after f.vals value lookup typed.typed slots (by simpa only [point.locals] using source) destination
      (by simpa only [destination] using capacity value lookup))
    intro out effect
    obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
    refine ⟨success, sameStore, samePlatform, pc,
      { f with code := after, vals := f.vals ++ [value] }, targets, next, output, false, (by omega), rfl,
      unchanged, represented, .ready nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _ (frame_references_localGet f localIndex.val value lookup), ?_,Or.inr ⟨_,_,rfl⟩,?_⟩
    · apply ConcreteSim.of_source
      exact simulation
    · exact FrameOwnershipClosure.local_get {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} after localIndex.val value lookup

end Itasca.Runtime.Interp.StructuredMachine

end

/-! ## Local Prefix -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std
theorem localGet_fetch {s raw compiled C targets next output} {f : Abs.AFrame}
    (index : Nat) (after : List instr)
    (point : FramePoint s raw {f with code := .LOCAL_GET (.mk_uN index)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases structuredCode_linear_inv (by rfl) point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,continuation⟩
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨ty,src,dst,localType,emittedEq,middleEq,source,position⟩ := linearEmission_localGet_inv index (emission_localGet_pure index head)
    refine ⟨Code.move ty dst src,?_,move_prefix ty dst src⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

theorem localWrite_fetch {s raw compiled C targets next output} {f : Abs.AFrame}
    (index : Nat) (keep : Bool) (after : List instr)
    (point : FramePoint s raw {f with code := (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index))::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  have linear : linearSource (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = true := by cases keep <;> rfl
  rcases structuredCode_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,continuation⟩
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨stack,ty,dst,src,shape,localType,emittedEq,middleEq,destination,source⟩ := linearEmission_localWrite_inv index keep (emission_localWrite_pure index keep head)
    refine ⟨Code.move ty dst src,?_,move_prefix ty dst src⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])
end Itasca.Runtime.Interp.StructuredMachine

end

/-! ## Local Write Owned -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std
theorem step_localWrite_owned_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (localIndex : U32) (keep : Bool) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.CoreTyped ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (targets' : List Code.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool), raw.pc.val < pc.val ∧ pending = false ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        Abs.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        (g = {f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after} ∨ ∃locals values, g = {f with code := after,locals := locals,vals := values}) ∧
        FrameOwnershipClosure {f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after} g ⦄ := by
  have linear : linearSource (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) = true := by cases keep <;> rfl
  rcases structuredCode_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after },
      targets, next, output, false, forward, rfl, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, ty, dst, src, shape, localType, emittedEq, middleEq, destination, source⟩ :=
      linearEmission_localWrite_inv localIndex.val keep (emission_localWrite_pure localIndex.val keep head)
    obtain ⟨front, value, valuesSplit, frontTypes, valueType⟩ := values_type_suffix f.vals stack ty shape
    obtain ⟨old, lookup, oldType⟩ := values_type_lookup f.locals localIndex.val ty (by simpa only [point.locals] using localType)
    have compatible : Code.valueType value = Code.valueType old := valueType.trans oldType.symm
    have frameTyped : Abs.FrameTyped s
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    have frameTyped' : Abs.FrameTyped s
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after, vals := front ++ [value] } [] := by
      simpa only [← valuesSplit] using frameTyped
    have typed' : Abs.ATyped ⟨s, ambient,
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after, vals := front ++ [value] } :: rest, []⟩ := by
      simpa only [← valuesSplit] using typed.typed
    have slots' : FrameSlots exec raw { f with vals := front ++ [value] } := by
      simpa only [← valuesSplit] using slots
    have nextFrame : Abs.FrameTyped s
        { f with code := after, locals := f.locals.set localIndex.val value, vals := if keep then front ++ [value] else front } [] := by
      cases keep with
      | false => exact Abs.local_set_frame_preservation frameTyped'
      | true => exact Abs.local_tee_frame_preservation frameTyped'
    have nextTyped := Abs.active_frame_preservation typed.typed nextFrame rfl
    have heights := frame_linear_heights frameTyped linear front (by
      rw [valuesSplit]
      cases keep <;> simp [linearInputs])
    have labelsAfter : LabelsMatch (if keep then front ++ [value] else front) f.labels targets := by
      have labels : LabelsMatch (front ++ [value]) f.labels targets := by simpa only [← valuesSplit] using point.labels
      cases keep with
      | true => exact labels
      | false => simpa only [List.append_nil, Bool.false_eq_true, ite_false] using labels.replace_suffix (after := []) heights
    have fetched : compiled.code.val[raw.pc.val]? = some (Code.move (Code.valueType value) dst src) := by
      simpa only [Nat.add_zero, valueType] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have sourcePosition : src.val = Code.slots ((f.locals ++ front).map Code.valueType) := by
      simpa only [point.locals,List.map_append, Code.slots_append, frontTypes] using source
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Code.move (Code.valueType value) dst src) last hf hi hc fetched pcBound
    intro pc hpc
    have nextPoint : FramePoint s { raw with pc := pc }
        { f with code := after, locals := f.locals.set localIndex.val value, vals := if keep then front ++ [value] else front }
        compiled C targets next output := by
      apply linear_continuation point pc (f.locals.set localIndex.val value)
        (if keep then front ++ [value] else front) after middle
      · simpa only [endpoint, hpc] using continuation
      · exact Code.valueTypes_set lookup compatible
      · cases keep <;> simp only [middleEq, Bool.false_eq_true, ite_false, ite_true, List.map_append,
          List.map_cons, List.map_nil, frontTypes, valueType]
      · exact labelsAfter
    apply WP.spec_mono (dispatch_localWrite_refines memory hooks floats allocator
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index raw
      localIndex src dst keep s ambient f rest after front value old lookup compatible typed' slots' sourcePosition (by simpa only [point.locals] using destination))
    intro out effect
    obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
    refine ⟨success, sameStore, samePlatform, pc,
      { f with code := after, locals := f.locals.set localIndex.val value, vals := if keep then front ++ [value] else front },
      targets, next, output, false, (by omega), rfl, unchanged, represented, .ready nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, Code.valueTypes_set lookup compatible⟩, .tail _ _ _ _ _ (frame_references_localWrite f localIndex.val front value keep valuesSplit), ?_,Or.inr ⟨_,_,rfl⟩,?_⟩
    · apply ConcreteSim.of_source
      simpa only [← valuesSplit] using simulation
    · cases keep
      · simpa only [Bool.false_eq_true,ite_false,←valuesSplit] using FrameOwnershipClosure.local_set f (.LOCAL_SET (.mk_uN localIndex.val)::after) after front value localIndex.val
      · simpa only [ite_true,←valuesSplit] using FrameOwnershipClosure.local_tee f (.LOCAL_TEE (.mk_uN localIndex.val)::after) after front value localIndex.val

end Itasca.Runtime.Interp.StructuredMachine

end

/-! ## Local Execution Owned -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_localGet_execution_owned_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (localIndex : U32)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,allowed⟩ := localGet_fetch localIndex.val after point
  have pcBound := program.fetched_bound instruction fetched
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]
    exact frameFound
  have binding := (machine.stack.top raw top).binding
  have capacity := structured_local_get_storage_capacity binding inst compiled found codeFound program.checked localIndex.val after point
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_localGet_owned_forward memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest localIndex after last frameFound found codeFound pcBound machine.typed slots capacity point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched allowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,forward,pendingEq,unchanged,represented,retained,typed,metadata,closure,simulation,shape,ownership⟩ := effect
  subst pending
  have uniform := simulation.uniform_forward forward (by scalar_tac)
  have covered : Abs.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | ⟨locals,values,same⟩
    · rw [same]; exact machine.core
    · rw [same]; exact StructuredMachine.SyntaxClosure.supported (SyntaxClosure.tail _ _ _ _ _) machine.core
  refine ⟨success,storeSame,platformSame,pc,g,false,?_,simulation,uniform,fun _ h => FrameOwnershipClosure.stateful ownership h,fun _ bounded => closure.codeBound bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

theorem step_localWrite_execution_owned_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (localIndex : U32) (keep : Bool)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,allowed⟩ := localWrite_fetch localIndex.val keep after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_localWrite_owned_forward memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest localIndex keep after last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched allowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,forward,pendingEq,unchanged,represented,retained,typed,metadata,closure,simulation,shape,ownership⟩ := effect
  subst pending
  have uniform := simulation.uniform_forward forward (by scalar_tac)
  have covered : Abs.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | ⟨locals,values,same⟩
    · rw [same]; exact machine.core
    · rw [same]; exact StructuredMachine.SyntaxClosure.supported (SyntaxClosure.tail _ _ _ _ _) machine.core
  refine ⟨success,storeSame,platformSame,pc,g,false,?_,simulation,uniform,fun _ h => FrameOwnershipClosure.stateful ownership h,fun _ bounded => closure.codeBound bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

end Itasca.Runtime.Interp.StructuredMachine

end
