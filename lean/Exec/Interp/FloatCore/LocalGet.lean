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

theorem step_localGet_float_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
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
    (point : FloatFramePoint s raw { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after }
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
        SourceClosure { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        (g = {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} ∨ ∃locals values, g = {f with code := after,locals := locals,vals := values}) ⦄ := by
  rcases structuredCode_linear_inv (by rfl) point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FloatFramePoint s { raw with pc := target }
        { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨ty, src, dst, localType, emittedEq, middleEq, source, position⟩ := linearEmission_localGet_inv localIndex.val (floatCoreEmission_localGet_pure localIndex.val head)
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
    have nextPoint : FloatFramePoint s { raw with pc := pc }
        { f with code := after, vals := f.vals ++ [value] }
        compiled C targets next output := by
      apply float_structured_linear_continuation point pc f.locals (f.vals ++ [value]) after middle
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
      { f with code := after, vals := f.vals ++ [value] }, targets, next, output, false,
      unchanged, represented, .ready nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _ (frame_references_localGet f localIndex.val value lookup), ?_,Or.inr ⟨_,_,rfl⟩⟩
    apply ConcreteSim.of_source
    exact simulation

end Exec.Interp