import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Machines.Slice.SliceCertified
import Exec.Interp.Relations.TypedOperands

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_sliceBinary_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (ty : Inn) (op : SliceBinary) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := (op.operation.source ty) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := (op.operation.source ty) :: after }
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
        SourceClosure { f with code := (op.operation.source ty) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := (op.operation.source ty) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ⦄ := by
  have linear : linearSource (op.operation.source ty) = true := by cases op <;> rfl
  rcases codeRel_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : StructuredFramePoint { raw with pc := target }
        { f with code := (op.operation.source ty) :: after } compiled functions targets next output :=
      ⟨point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := (op.operation.source ty) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linearEmission_slice_inv ty op head
    have frameTyped : Abs.FrameTyped s { f with code := op.operation.source ty :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    obtain ⟨front, a, b, split, frontTypes, ha, hb⟩ := frame_integer_pair frameTyped stack ty shape
    have valuesSplit : f.vals = front ++ [Abs.integerVal ty a, Abs.integerVal ty b] := split
    have typed' : Abs.ATyped ⟨s, ambient,
        { f with code := op.operation.source ty :: after, vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩ := by
      simpa only [← valuesSplit] using typed
    have slots' : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } := by
      simpa only [← valuesSplit] using slots
    have leftPosition : left.val = Code.slots ((f.locals ++ front).map Code.valueType) := by
      simpa only [List.map_append, Code.slots_append, frontTypes] using leftPos
    have rightPosition : right.val = Code.slots ((f.locals ++ front).map Code.valueType) + 1 := by omega
    have fetched : compiled.code.val[raw.pc.val]? = some (Code.IntegerBinary.target ty op.operation left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have heights := frame_linear_heights frameTyped linear front (by
      rw [valuesSplit]
      cases op <;> simp [SliceBinary.operation, Code.IntegerBinary.source, linearInputs])
    have labelsAfter : LabelsMatch (front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)]) f.labels targets := by
      have labels : LabelsMatch (front ++ [Abs.integerVal ty a, Abs.integerVal ty b]) f.labels targets := by
        simpa only [← valuesSplit] using point.labels
      exact labels.replace_suffix heights
    have sourceStep : Abs.astep
        ⟨s, ambient, { f with code := op.operation.source ty :: after, vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩ = .next
        ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } :: rest, []⟩ := by
      have hia := Abs.integer_accepts ty a ha
      have hib := Abs.integer_accepts ty b hb
      have width : (if numtype_Inn ty = numtype.I32 then 32 else 64) = Abs.integerWidth ty := by cases ty <;> rfl
      have parts : front ++ [Abs.integerVal ty a, Abs.integerVal ty b] =
          (front ++ [Abs.integerVal ty a]) ++ [Abs.integerVal ty b] := by simp
      cases op <;>
        simp only [SliceBinary.operation, SliceBinary.result, SliceBinary.resultType,
          Code.IntegerBinary.source, Abs.astep, parts, Abs.pop_append, hia, hib,
          width, ite_true, Abs.integerBinary, Abs.advance, decide_eq_true_eq]
    have slice : Abs.SliceInstr (op.operation.source ty) := by
      cases op
      · exact .add ty
      · exact .sub ty
      · exact .eq ty
      · exact .lt_u ty
    have nextTyped := Abs.instruction_preservation s ambient
      { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } rest _ after _ slice typed' sourceStep
    apply WP.spec_mono (step_sliceBinary_refines memory hooks floats allocator exec store platform index raw inst compiled
      left right s ambient f rest after front ty op a b last hf hi hc fetched pcBound ha hb typed' slots' leftPosition rightPosition)
    intro out effect
    obtain ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged⟩, simulation⟩ := effect
    have nextPoint : StructuredFramePoint { raw with pc := pc }
        { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] }
        compiled functions targets next output := by
      apply structured_linear_continuation point pc f.locals
        (front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)]) after middle
      · simpa only [endpoint, hpc] using continuation
      · rfl
      · have valueType (ity : Inn) (n : Nat) : Code.valueType (Abs.integerVal ity n) = Code.integerType ity := by cases ity <;> rfl
        simp only [middleEq, List.map_append, List.map_cons, List.map_nil, valueType, frontTypes]
      · exact labelsAfter
    refine ⟨success, sameStore, samePlatform, pc,
      { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] },
      targets, next, output, false, unchanged, represented, .ready nextPoint, nextTyped, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _ (frame_references_numeric f front _ _ _ valuesSplit), ?_⟩
    apply ConcreteSim.of_source
    simpa only [← valuesSplit] using simulation

end Exec.Interp
