import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Relations.ConstCertified
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_const32_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : U32) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) < exec.slots.length)
    (point : StructuredFramePoint raw { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after }
      compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (targets' : List Code.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint { raw with pc := pc } g compiled functions targets' next' output' pending ∧
        Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ⦄ := by
  rcases codeRel_linear_inv (by rfl) point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : StructuredFramePoint { raw with pc := target }
        { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } compiled functions targets next output :=
      ⟨point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨dst, emittedEq, middleEq, position⟩ := linearEmission_const32_inv value head
    have destination : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType) := by
      simpa only [List.map_append, Code.slots_append] using position
    have fetched : compiled.code.val[raw.pc.val]? = some (.Const32 dst value) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have frameTyped : Abs.FrameTyped s { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have nextTyped := Abs.const_preservation s ambient f rest after .I32 (.mk_num__0 .I32 (.mk_uN value.val)) [] typed
    have labelsAfter : LabelsMatch (f.vals ++ [Abs.integerVal .I32 value.val]) f.labels targets := by
      have old : LabelsMatch (f.vals ++ []) f.labels targets := by simpa only [List.append_nil] using point.labels
      have heights := Abs.frameTyped_heights frameTyped
      exact old.replace_suffix heights
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const32 dst value) last hf hi hc fetched pcBound
    intro pc hpc
    have nextPoint : StructuredFramePoint { raw with pc := pc }
        { f with code := after, vals := f.vals ++ [Abs.integerVal .I32 value.val] }
        compiled functions targets next output := by
      apply structured_linear_continuation point pc f.locals (f.vals ++ [Abs.integerVal .I32 value.val]) after middle
      · simpa only [endpoint, hpc] using continuation
      · rfl
      · simp only [middleEq, List.map_append, List.map_cons, List.map_nil, Abs.integerVal, Code.valueType, numtype_Inn, valtype_numtype]
      · exact labelsAfter
    apply WP.spec_mono (dispatch_const32_refines memory hooks floats allocator
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index raw dst value
      s ambient f rest after typed slots destination (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
    refine ⟨success, sameStore, samePlatform, pc,
      { f with code := after, vals := f.vals ++ [Abs.integerVal .I32 value.val] }, targets, next, output, false,
      unchanged, represented, .ready nextPoint, nextTyped, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _ (frame_references_numeric f f.vals [] _ _ (by simp)), ?_⟩
    apply ConcreteSim.of_source
    exact simulation

end Exec.Interp
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_const64_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : U64) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) < exec.slots.length)
    (point : StructuredFramePoint raw { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after }
      compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (targets' : List Code.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint { raw with pc := pc } g compiled functions targets' next' output' pending ∧
        Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ⦄ := by
  rcases codeRel_linear_inv (by rfl) point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : StructuredFramePoint { raw with pc := target }
        { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } compiled functions targets next output :=
      ⟨point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨dst, emittedEq, middleEq, position⟩ := linearEmission_const64_inv value head
    have destination : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType) := by
      simpa only [List.map_append, Code.slots_append] using position
    have fetched : compiled.code.val[raw.pc.val]? = some (.Const64 dst value) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have frameTyped : Abs.FrameTyped s { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have nextTyped := Abs.const_preservation s ambient f rest after .I64 (.mk_num__0 .I64 (.mk_uN value.val)) [] typed
    have labelsAfter : LabelsMatch (f.vals ++ [Abs.integerVal .I64 value.val]) f.labels targets := by
      have old : LabelsMatch (f.vals ++ []) f.labels targets := by simpa only [List.append_nil] using point.labels
      have heights := Abs.frameTyped_heights frameTyped
      exact old.replace_suffix heights
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const64 dst value) last hf hi hc fetched pcBound
    intro pc hpc
    have nextPoint : StructuredFramePoint { raw with pc := pc }
        { f with code := after, vals := f.vals ++ [Abs.integerVal .I64 value.val] }
        compiled functions targets next output := by
      apply structured_linear_continuation point pc f.locals (f.vals ++ [Abs.integerVal .I64 value.val]) after middle
      · simpa only [endpoint, hpc] using continuation
      · rfl
      · simp only [middleEq, List.map_append, List.map_cons, List.map_nil, Abs.integerVal, Code.valueType, numtype_Inn, valtype_numtype]
      · exact labelsAfter
    apply WP.spec_mono (dispatch_const64_refines memory hooks floats allocator
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index raw dst value
      s ambient f rest after typed slots destination (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
    refine ⟨success, sameStore, samePlatform, pc,
      { f with code := after, vals := f.vals ++ [Abs.integerVal .I64 value.val] }, targets, next, output, false,
      unchanged, represented, .ready nextPoint, nextTyped, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _ (frame_references_numeric f f.vals [] _ _ (by simp)), ?_⟩
    apply ConcreteSim.of_source
    exact simulation

end Exec.Interp
