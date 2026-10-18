import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.FloatCore.LocalInversion
import Exec.Abs.Core.Typing
import Exec.Interp.FloatCore.SuspendedPoint
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Relations.LocalCertified
import Exec.Interp.Relations.ValueLookup
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_localWrite_float_core_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
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
    (point : FloatFramePoint s raw { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (targets' : List Code.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FloatCoreControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
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
    have targetPoint : FloatFramePoint s { raw with pc := target }
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, ty, dst, src, shape, localType, emittedEq, middleEq, destination, source⟩ :=
      linearEmission_localWrite_inv localIndex.val keep (floatCoreEmission_localWrite_pure localIndex.val keep head)
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
    have nextPoint : FloatFramePoint s { raw with pc := pc }
        { f with code := after, locals := f.locals.set localIndex.val value, vals := if keep then front ++ [value] else front }
        compiled C targets next output := by
      apply float_structured_linear_continuation point pc (f.locals.set localIndex.val value)
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
      targets, next, output, false, unchanged, represented, .ready nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, Code.valueTypes_set lookup compatible⟩, .tail _ _ _ _ _ (frame_references_localWrite f localIndex.val front value keep valuesSplit), ?_,Or.inr ⟨_,_,rfl⟩,?_⟩
    · apply ConcreteSim.of_source
      simpa only [← valuesSplit] using simulation
    · cases keep
      · simpa only [Bool.false_eq_true,ite_false,←valuesSplit] using FrameOwnershipClosure.local_set f (.LOCAL_SET (.mk_uN localIndex.val)::after) after front value localIndex.val
      · simpa only [ite_true,←valuesSplit] using FrameOwnershipClosure.local_tee f (.LOCAL_TEE (.mk_uN localIndex.val)::after) after front value localIndex.val

end Exec.Interp
