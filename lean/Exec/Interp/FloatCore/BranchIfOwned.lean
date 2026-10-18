import Exec.Interp.Core.BoundClosure
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.FloatCore.BranchInversion
import Exec.Interp.FloatCore.BranchPoint
import Exec.Interp.FloatCore.SyntaxClosure
import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Interp.FloatCore.SuspendedPoint
import Exec.Abs.Core.Typing
import Exec.Interp.Control.StructuredBranch
import Exec.Interp.Control.BranchIfInversion
import Exec.Interp.Control.BranchConditionStep
import Exec.Interp.Relations.TypedOperands

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_branchIf_float_core_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (depth : Nat) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.CoreTyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FloatFramePoint s raw { f with code := .BR_IF (.mk_uN depth) :: after }
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
        FloatCoreSyntaxClosure { f with code := .BR_IF (.mk_uN depth) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        FrameOwnershipClosure {f with code := .BR_IF (.mk_uN depth) :: after} g ∧
        FrameBoundClosure {f with code := .BR_IF (.mk_uN depth) :: after} g ⦄ := by
  rcases floatCoreCodeRel_branchIf_inv point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FloatFramePoint s { raw with pc := target }
        { f with code := .BR_IF (.mk_uN depth) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .BR_IF (.mk_uN depth) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,.refl _,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨before, target, dst, src, count, cond, resume, shape, staticLookup, live, layout,
      condition, fragment, continuation⟩ := branch
    have frameTyped : Abs.FrameTyped s { f with code := .BR_IF (.mk_uN depth) :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨values, bits, valueSplit, valueTypes, bitsBound⟩ := frame_integer_suffix frameTyped before .I32 shape
    have valueSplit : f.vals = values ++ [Abs.integerVal .I32 bits] := valueSplit
    have typed' : Abs.ATyped ⟨s, ambient,
        { f with code := .BR_IF (.mk_uN depth) :: after, vals := values ++ [Abs.integerVal .I32 bits] } :: rest, []⟩ := by
      simpa only [← valueSplit] using typed.typed
    have slots' : FrameSlots exec raw { f with vals := values ++ [Abs.integerVal .I32 bits] } := by
      simpa only [← valueSplit] using slots
    have position : cond.val = Code.slots ((f.locals ++ values).map Code.valueType) := by
      simpa only [point.locals,List.map_append, Code.slots_append, valueTypes] using condition
    have sourceStep := branchIf_source_step s ambient f rest after depth values bits bitsBound
    have typedAfter := Abs.instruction_preservation s ambient
      { f with vals := values ++ [Abs.integerVal .I32 bits] } rest (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed' sourceStep
    have frameAfter : Abs.FrameTyped s
        { f with code := if bits = 0 then after else .BR (.mk_uN depth) :: after, vals := values } [] := by
      cases typedAfter.frames with | cons h _ => exact h
    have labelsAfter : LabelsMatch values f.labels targets := by
      have old : LabelsMatch (values ++ [Abs.integerVal .I32 bits]) f.labels targets := by
        simpa only [← valueSplit] using point.labels
      have h := old.replace_suffix (after := []) (Abs.frameTyped_heights frameAfter)
      simpa only [List.append_nil] using h
    have layout' : Code.BranchLayout (f.locals.map Code.valueType) (values.map Code.valueType) target dst src count := by
      simpa only [point.locals,valueTypes] using layout
    have ownershipDrop : ∀ code labels, FrameOwnershipClosure {f with code := .BR_IF (.mk_uN depth) :: after}
        {f with code,labels,vals := values} := by
      intro code labels
      apply FrameOwnershipClosure.subsets
      · intro value member; exact Or.inl member
      · intro value member; exact Or.inr (by simp [valueSplit,member])
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · obtain ⟨label, front, discarded, results, lookup, matching, split, height, arity, types,
        destination, source, size⟩ := labelsAfter.branchLayout f.locals depth target staticLookup dst src count layout'
      have typedSplit : Abs.ATyped ⟨s, ambient,
          { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 bits] } :: rest, []⟩ := by
        simpa only [split] using typed'
      have slotsSplit : FrameSlots exec raw { f with vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 bits] } := by
        simpa only [split] using slots'
      have labelsSplit : LabelsMatch (front ++ discarded ++ results) f.labels targets := by simpa only [split] using labelsAfter
      have frameSplit : Abs.FrameTyped s
          { f with code := if bits = 0 then after else .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } [] := by
        simpa only [split] using frameAfter
      obtain ⟨actual, targetNext, targetOutput, actualAt, _, targetPoint⟩ :=
        float_core_branch_target_point (raw := raw) (f := { f with code := if bits = 0 then after else .BR (.mk_uN depth) :: after }) front discarded results point.bindings point.locals labelsSplit point.code.targets point.code.normal frameSplit
          depth label lookup height types
          (by intro found lookup; have same : found = target := Option.some.inj (lookup.symm.trans staticLookup); subst found; exact live)
      have same : actual = target := Option.some.inj (actualAt.symm.trans staticLookup)
      subst actual
      have fetched : compiled.code.val[raw.pc.val]? = some (.JumpIfNonZero cond target.target) := by
        simpa only [Nat.add_zero] using fragment.fetch
          (index := 0) (by simp only [Code.branchIfInstructions, if_pos noCopy, List.getElem?_cons_zero])
      have resumePc : resume.val = raw.pc.val + 1 := by
        obtain ⟨_, _, _, _, h⟩ := fragment
        simpa only [Code.branchIfInstructions, if_pos noCopy, List.length_singleton] using h
      apply WP.spec_mono (step_branchIfNoCopy_refines memory hooks floats allocator exec store platform
        index raw inst compiled cond target.target bits s ambient f rest after depth label front discarded results
        last hf hi hc pcBound fetched bitsBound lookup height arity types
        (branch_no_transfer destination source size noCopy) (by simpa only [split, List.append_assoc] using position)
        typedSplit slotsSplit)
      intro out effect
      obtain ⟨success, sameStore, samePlatform, represented, ⟨pc, hpc, exactState⟩, typedNext, simulation⟩ := effect
      by_cases zero : bits = 0
      · have pcResume : pc = resume := UScalar.eq_of_val_eq (hpc.trans resumePc.symm)
        subst pc
        simp only [if_pos zero] at exactState
        have nextPoint : FloatFramePoint s { raw with pc := resume } { f with code := after, vals := values }
            compiled C targets next output :=
          ⟨point.bindings,point.locals,labelsAfter, ⟨by simpa only [valueTypes] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
        refine ⟨success, sameStore, samePlatform, resume, { f with code := after, vals := values }, targets,
          next, output, false, ?_, ?_, .ready nextPoint, ?_, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _, ?_,ownershipDrop _ _,.tail _ _ _ _ _⟩
        · rw [exactState]
        · simpa only [FrameSlots, branchIfFrame, if_pos zero, ← split] using represented
        · exact ⟨by simpa only [branchIfFrame, if_pos zero, ← split] using typedNext,typed.contents⟩
        · apply ConcreteSim.of_source
          simpa only [branchIfFrame, if_pos zero, ← split, ← valueSplit] using simulation
      · simp only [if_neg zero] at exactState
        refine ⟨success, sameStore, samePlatform, target.target,
          { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results },
          targets.drop (depth + 1), targetNext, targetOutput, false, ?_, ?_, .ready ?_, ?_, ⟨rfl, rfl, rfl, rfl⟩, .branch { f with code := .BR_IF (.mk_uN depth) :: after } depth label lookup _, ?_,?_,.branch {f with code := .BR_IF (.mk_uN depth)::after} depth label lookup _⟩
        · rw [exactState]
        · simpa only [FrameSlots, branchIfFrame, if_neg zero] using represented
        · exact targetPoint
        · exact ⟨by simpa only [branchIfFrame, if_neg zero] using typedNext,typed.contents⟩
        · apply ConcreteSim.of_source
          simpa only [branchIfFrame, if_neg zero, ← split, ← valueSplit] using simulation
        · apply FrameOwnershipClosure.subsets
          · intro value member; exact Or.inl member
          · intro value member
            apply Or.inr
            simp only [valueSplit,split,List.mem_append] at member ⊢
            tauto
    · have fetched : compiled.code.val[raw.pc.val]? = some (.JumpIfZero cond resume) := by
        simpa only [Nat.add_zero] using fragment.fetch
          (index := 0) (by simp only [Code.branchIfInstructions, if_neg noCopy, List.getElem?_cons_zero])
      have parts : Code.branchIfInstructions dst src count target.target cond resume =
          [.JumpIfZero cond resume] ++ Code.branchInstructions dst src count target.target := by
        simp only [Code.branchIfInstructions, Code.branchInstructions, if_neg noCopy, List.cons_append, List.nil_append]
      obtain ⟨guard, branchFragment⟩ := fragment.split parts
      apply WP.spec_mono (step_branchGuard_refines memory hooks floats allocator exec store platform
        index raw inst compiled cond resume bits s ambient f rest after depth values last hf hi hc pcBound
        fetched bitsBound position typed' slots')
      intro out effect
      obtain ⟨success, sameStore, samePlatform, represented, ⟨pc, hpc, exactState⟩, simulation⟩ := effect
      have branchPoint : FloatFramePoint s { raw with pc := pc }
          { f with code := .BR (.mk_uN depth) :: after, vals := values } compiled C targets next output := by
        refine ⟨point.bindings,point.locals,labelsAfter, ⟨?_, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
        apply Code.StructuredCode.branch staticLookup live (by simpa only [point.locals] using layout')
        · simpa only [hpc, List.length_singleton] using branchFragment
        · exact continuation.pc_le_next
        · exact continuation.next_le_length
      have resumePoint : FloatFramePoint s { raw with pc := resume }
          { f with code := after, vals := values } compiled C targets next output :=
        ⟨point.bindings,point.locals,labelsAfter, ⟨by simpa only [valueTypes] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
      refine ⟨success, sameStore, samePlatform, (if bits = 0 then resume else pc),
        { f with code := if bits = 0 then after else .BR (.mk_uN depth) :: after, vals := values },
        targets, next, output, false, ?_, represented, .ready ?_, ⟨typedAfter,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_,ownershipDrop _ _,?_⟩
      · rw [exactState]
      · by_cases zero : bits = 0
        · simpa only [if_pos zero] using resumePoint
        · simpa only [if_neg zero] using branchPoint
      · by_cases zero : bits = 0
        · simpa only [if_pos zero] using FloatCoreSyntaxClosure.tail f (.BR_IF (.mk_uN depth)) after f.locals values
        · simpa only [if_neg zero] using FloatCoreSyntaxClosure.replace f (.BR_IF (.mk_uN depth)) (.BR (.mk_uN depth)) after f.locals values (.core (.slice (.br _)))
      · apply ConcreteSim.of_source
        simpa only [← valueSplit] using simulation
      · by_cases zero : bits = 0
        · simpa only [if_pos zero] using FrameBoundClosure.tail f (.BR_IF (.mk_uN depth)) after f.locals values
        · simpa only [if_neg zero] using FrameBoundClosure.replace f (.BR_IF (.mk_uN depth)) (.BR (.mk_uN depth)) after f.locals values (by simp)

end Exec.Interp
