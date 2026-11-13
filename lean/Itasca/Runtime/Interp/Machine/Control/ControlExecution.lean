import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Interp.Machine.Retention.CodeBounds
import Itasca.Runtime.Interp.Machine.Retention.Ownership
import Itasca.Runtime.Interp.Machine.Control.BranchPoint
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Interp.Machine.Coverage.RecordingHeads
import Itasca.Runtime.SourceMachine.Core.SelectPositive
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Spec.Integer

/-!
Sections, each formerly its own module: BranchIfOwned, BranchOwned, If, Loop, ControlExecution.
-/

/-! ## BranchIfOwned -/

section

/-!
Conditional-branch execution with retained ownership.

Main declarations: `step_branch_if_owned_uniform`. A direct consumer is `Interp.Machine.Control.ControlExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem step_branch_if_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (depth : Nat) (after : List instr) (branchAllowed : SourceMachine.BinaryInstr (.BR (.mk_uN depth)))
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := .BR_IF (.mk_uN depth) :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (targets' : List Compiler.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SyntaxClosure { f with code := .BR_IF (.mk_uN depth) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending
          ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth)::after}::rest,[]⟩
          ⟨s,ambient,g::rest,[]⟩ [] ∧
        FrameOwnershipClosure {f with code := .BR_IF (.mk_uN depth) :: after} g ∧
        FrameBoundClosure {f with code := .BR_IF (.mk_uN depth) :: after} g ⦄ := by
  rcases code_rel_branch_if_inv point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := .BR_IF (.mk_uN depth) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .BR_IF (.mk_uN depth) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,UniformConcreteSim.forward rfl forward (by scalar_tac),.refl _,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨before, target, dst, src, count, cond, resume, shape, staticLookup, live, layout,
      condition, fragment, continuation⟩ := branch
    have frameTyped : SourceMachine.FrameTyped s { f with code := .BR_IF (.mk_uN depth) :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨values, bits, valueSplit, valueTypes, bitsBound⟩ := frame_integer_suffix frameTyped before .I32 shape
    have valueSplit : f.vals = values ++ [SourceMachine.integerVal .I32 bits] := valueSplit
    have typed' : SourceMachine.ATyped ⟨s, ambient,
        { f with code := .BR_IF (.mk_uN depth) :: after, vals := values ++ [SourceMachine.integerVal .I32 bits] } :: rest, []⟩ := by
      simpa only [← valueSplit] using typed.typed
    have slots' : FrameSlots exec raw { f with vals := values ++ [SourceMachine.integerVal .I32 bits] } := by
      simpa only [← valueSplit] using slots
    have position : cond.val = Compiler.slots ((f.locals ++ values).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append, Compiler.slots_append, valueTypes] using condition
    have sourceStep := branch_if_source_step s ambient f rest after depth values bits bitsBound
    have sourcePositive := SourceMachine.typed_br_if_positive s ambient {f with vals := values ++ [SourceMachine.integerVal .I32 bits]}
      rest after depth _ typed' sourceStep
    have testUniform (pc : U32) : UniformConcreteSim raw.pc.val pc.val false false
        ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth)::after}::rest,[]⟩
        ⟨s,ambient,{f with code := if bits = 0 then after else .BR (.mk_uN depth)::after,vals := values}::rest,[]⟩ [] := by
      apply UniformConcreteSim.single
      simpa only [← valueSplit] using sourcePositive
    have typedAfter := SourceMachine.instruction_preservation s ambient
      { f with vals := values ++ [SourceMachine.integerVal .I32 bits] } rest (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed' sourceStep
    have frameAfter : SourceMachine.FrameTyped s
        { f with code := if bits = 0 then after else .BR (.mk_uN depth) :: after, vals := values } [] := by
      cases typedAfter.frames with | cons h _ => exact h
    have labelsAfter : LabelsMatch values f.labels targets := by
      have old : LabelsMatch (values ++ [SourceMachine.integerVal .I32 bits]) f.labels targets := by
        simpa only [← valueSplit] using point.labels
      have h := old.replace_suffix (after := []) (SourceMachine.frame_typed_heights frameAfter)
      simpa only [List.append_nil] using h
    have layout' : Compiler.BranchLayout (f.locals.map Compiler.valueType) (values.map Compiler.valueType) target dst src count := by
      simpa only [point.locals,valueTypes] using layout
    have ownershipDrop : ∀ code labels, FrameOwnershipClosure {f with code := .BR_IF (.mk_uN depth) :: after}
        {f with code,labels,vals := values} := by
      intro code labels
      apply FrameOwnershipClosure.subsets
      · intro value member; exact Or.inl member
      · intro value member; exact Or.inr (by simp [valueSplit,member])
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · obtain ⟨label, front, discarded, results, lookup, matching, split, height, arity, types,
        destination, source, size⟩ := labelsAfter.branch_layout f.locals depth target staticLookup dst src count layout'
      have typedSplit : SourceMachine.ATyped ⟨s, ambient,
          { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 bits] } :: rest, []⟩ := by
        simpa only [split] using typed'
      have slotsSplit : FrameSlots exec raw { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 bits] } := by
        simpa only [split] using slots'
      have labelsSplit : LabelsMatch (front ++ discarded ++ results) f.labels targets := by simpa only [split] using labelsAfter
      have frameSplit : SourceMachine.FrameTyped s
          { f with code := if bits = 0 then after else .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } [] := by
        simpa only [split] using frameAfter
      obtain ⟨actual, targetNext, targetOutput, actualAt, _, targetPoint⟩ :=
        branch_target_point (raw := raw) (f := { f with code := if bits = 0 then after else .BR (.mk_uN depth) :: after }) front discarded results point.bindings point.locals labelsSplit point.code.targets point.code.normal frameSplit
          depth label lookup height types
          (by intro found lookup; have same : found = target := Option.some.inj (lookup.symm.trans staticLookup); subst found; exact live)
      have same : actual = target := Option.some.inj (actualAt.symm.trans staticLookup)
      subst actual
      have fetched : compiled.code.val[raw.pc.val]? = some (.JumpIfNonZero cond target.target) := by
        simpa only [Nat.add_zero] using fragment.fetch
          (index := 0) (by simp only [Compiler.branchIfInstructions, if_pos noCopy, List.getElem?_cons_zero])
      have fusedUniform (pc : U32) : UniformConcreteSim raw.pc.val pc.val false false
          ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth)::after}::rest,[]⟩
          ⟨s,ambient,branchIfFrame f after depth label front discarded results bits::rest,[]⟩ [] := by
        obtain ⟨count,positive,steps⟩ := branch_if_source_positive s ambient f rest after depth label front discarded results bits
          bitsBound lookup height arity types typedSplit
        apply UniformConcreteSim.of_steps positive
        simpa only [← split,← valueSplit] using steps
      have resumePc : resume.val = raw.pc.val + 1 := by
        obtain ⟨_, _, _, _, h⟩ := fragment
        simpa only [Compiler.branchIfInstructions, if_pos noCopy, List.length_singleton] using h
      apply WP.spec_mono (step_branch_if_no_copy_refines memory hooks floats allocator exec store platform
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
        have nextPoint : FramePoint s { raw with pc := resume } { f with code := after, vals := values }
            compiled C targets next output :=
          ⟨point.bindings,point.locals,labelsAfter, ⟨by simpa only [valueTypes] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
        refine ⟨success, sameStore, samePlatform, resume, { f with code := after, vals := values }, targets,
          next, output, false, ?_, ?_, .ready nextPoint, ?_, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _, ?_,(by simpa only [branchIfFrame,if_pos zero,← split] using fusedUniform resume),ownershipDrop _ _,.tail _ _ _ _ _⟩
        · rw [exactState]
        · simpa only [FrameSlots, branchIfFrame, if_pos zero, ← split] using represented
        · exact ⟨by simpa only [branchIfFrame, if_pos zero, ← split] using typedNext,typed.contents⟩
        · apply ConcreteSim.of_source
          simpa only [branchIfFrame, if_pos zero, ← split, ← valueSplit] using simulation
      · simp only [if_neg zero] at exactState
        refine ⟨success, sameStore, samePlatform, target.target,
          { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results },
          targets.drop (depth + 1), targetNext, targetOutput, false, ?_, ?_, .ready ?_, ?_, ⟨rfl, rfl, rfl, rfl⟩, .branch { f with code := .BR_IF (.mk_uN depth) :: after } depth label lookup _, ?_,(by simpa only [branchIfFrame,if_neg zero] using fusedUniform target.target),?_,.branch {f with code := .BR_IF (.mk_uN depth)::after} depth label lookup _⟩
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
          (index := 0) (by simp only [Compiler.branchIfInstructions, if_neg noCopy, List.getElem?_cons_zero])
      have parts : Compiler.branchIfInstructions dst src count target.target cond resume =
          [.JumpIfZero cond resume] ++ Compiler.branchInstructions dst src count target.target := by
        simp only [Compiler.branchIfInstructions, Compiler.branchInstructions, if_neg noCopy, List.cons_append, List.nil_append]
      obtain ⟨guard, branchFragment⟩ := fragment.split parts
      apply WP.spec_mono (step_branch_guard_refines memory hooks floats allocator exec store platform
        index raw inst compiled cond resume bits s ambient f rest after depth values last hf hi hc pcBound
        fetched bitsBound position typed' slots')
      intro out effect
      obtain ⟨success, sameStore, samePlatform, represented, ⟨pc, hpc, exactState⟩, simulation⟩ := effect
      have branchPoint : FramePoint s { raw with pc := pc }
          { f with code := .BR (.mk_uN depth) :: after, vals := values } compiled C targets next output := by
        refine ⟨point.bindings,point.locals,labelsAfter, ⟨?_, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
        apply Compiler.StructuredCode.branch staticLookup live (by simpa only [point.locals] using layout')
        · simpa only [hpc, List.length_singleton] using branchFragment
        · exact continuation.pc_le_next
        · exact continuation.next_le_length
      have resumePoint : FramePoint s { raw with pc := resume }
          { f with code := after, vals := values } compiled C targets next output :=
        ⟨point.bindings,point.locals,labelsAfter, ⟨by simpa only [valueTypes] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
      refine ⟨success, sameStore, samePlatform, (if bits = 0 then resume else pc),
        { f with code := if bits = 0 then after else .BR (.mk_uN depth) :: after, vals := values },
        targets, next, output, false, ?_, represented, .ready ?_, ⟨typedAfter,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_,testUniform _,ownershipDrop _ _,?_⟩
      · rw [exactState]
      · by_cases zero : bits = 0
        · simpa only [if_pos zero] using resumePoint
        · simpa only [if_neg zero] using branchPoint
      · by_cases zero : bits = 0
        · simpa only [if_pos zero] using SyntaxClosure.tail f (.BR_IF (.mk_uN depth)) after f.locals values
        · simpa only [if_neg zero] using SyntaxClosure.replace f (.BR_IF (.mk_uN depth)) (.BR (.mk_uN depth)) after f.locals values branchAllowed
      · apply ConcreteSim.of_source
        simpa only [← valueSplit] using simulation
      · by_cases zero : bits = 0
        · simpa only [if_pos zero] using FrameBoundClosure.tail f (.BR_IF (.mk_uN depth)) after f.locals values
        · simpa only [if_neg zero] using FrameBoundClosure.replace f (.BR_IF (.mk_uN depth)) (.BR (.mk_uN depth)) after f.locals values (by simp)

end Itasca.Runtime.Interp.Machine

end

/-! ## BranchOwned -/

section

/-!
A complete BR iteration, including compiler-elided copies and forward administrative skips. All operand decomposition, slots and target continuation come from retained structured code evidence and generated source typing.

Main declarations: `step_branch_owned_uniform`. A direct consumer is `Interp.Machine.Control.ControlExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- A complete BR iteration, including compiler-elided copies and forward
administrative skips. All operand decomposition, slots and target continuation
come from retained structured code evidence and generated source typing. -/
theorem step_branch_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (depth : Nat) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType) ≤ exec.slots.length)
    (point : FramePoint s raw { f with code := .BR (.mk_uN depth) :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (targets' : List Compiler.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SyntaxClosure { f with code := .BR (.mk_uN depth) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending
          ⟨s,ambient,{f with code := .BR (.mk_uN depth)::after}::rest,[]⟩
          ⟨s,ambient,g::rest,[]⟩ [] ∧
        FrameOwnershipClosure {f with code := .BR (.mk_uN depth) :: after} g ∧
        FrameBoundClosure {f with code := .BR (.mk_uN depth) :: after} g ⦄ := by
  rcases code_rel_branch_inv point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := .BR (.mk_uN depth) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .BR (.mk_uN depth) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,UniformConcreteSim.forward rfl forward (by scalar_tac),.refl _,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨target, dst, src, count, fragmentEnd, staticLookup, live, layout, fragment, remaining⟩ := branch
    obtain ⟨label, front, discarded, results, lookup, matching, split, height, arity, types,
      destination, source, size⟩ := point.labels.branch_layout f.locals depth target staticLookup dst src count (by simpa only [point.locals] using layout)
    have frameTyped : SourceMachine.FrameTyped s { f with code := .BR (.mk_uN depth) :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    have point' : FramePoint s raw { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results }
        compiled C targets next output := by simpa only [← split] using point
    have typed' : SourceMachine.ATyped ⟨s, ambient,
        { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩ := by
      simpa only [← split] using typed.typed
    have slots' : FrameSlots exec raw { f with vals := front ++ discarded ++ results } := by simpa only [← split] using slots
    have capacity' : raw.base.val + Compiler.slots ((f.locals ++ front ++ discarded ++ results).map Compiler.valueType) ≤ exec.slots.length := by
      have valuesSplit : f.vals = front ++ discarded ++ results := split
      simpa only [valuesSplit, List.append_assoc] using capacity
    obtain ⟨actual, targetNext, targetOutput, actualAt, _, targetPoint⟩ := point'.branch front discarded results
      (by simpa only [← split] using frameTyped) depth label lookup height types
      (by intro found lookup; have same : found = target := Option.some.inj (lookup.symm.trans staticLookup); subst found; exact live)
    have same : actual = target := Option.some.inj (actualAt.symm.trans staticLookup)
    subst actual
    have sourceStep := branch_source_step s ambient f rest after depth label front discarded results lookup height arity types
    have sourceCounted := SourceMachine.typed_branch_simulation s ambient {f with vals := front ++ discarded ++ results}
      rest after depth _ typed' sourceStep
    have uniform (pc : U32) (pending : Bool) : UniformConcreteSim raw.pc.val pc.val false pending
        ⟨s,ambient,{f with code := .BR (.mk_uN depth)::after}::rest,[]⟩
        ⟨s,ambient,{f with code := label.cont ++ label.after,labels := f.labels.drop (depth+1),vals := front ++ results}::rest,[]⟩ [] := by
      apply UniformConcreteSim.of_steps (by omega : 0 < depth+1)
      simpa only [← split] using sourceCounted
    have nextTyped := SourceMachine.instruction_preservation s ambient { f with vals := front ++ discarded ++ results } rest
      (.BR (.mk_uN depth)) after _ (.br _) typed' sourceStep
    change f.vals = front ++ discarded ++ results at split
    have ownership : FrameOwnershipClosure {f with code := .BR (.mk_uN depth) :: after}
        {f with code := label.cont ++ label.after,labels := f.labels.drop (depth+1),vals := front ++ results} := by
      apply FrameOwnershipClosure.subsets
      · intro value member; exact Or.inl member
      · intro value member
        apply Or.inr
        simp only [split,List.mem_append] at member ⊢
        tauto
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · have fetched : compiled.code.val[raw.pc.val]? = some (.Jump target.target) := by
        simpa only [Nat.add_zero] using fragment.fetch
          (index := 0) (by simp only [Compiler.branchInstructions, if_pos noCopy, List.getElem?_cons_zero])
      have empty := branch_no_transfer destination source size noCopy
      apply WP.spec_mono (step_branch_no_copy_refines memory hooks floats allocator exec store platform
        index raw target.target inst compiled s ambient f rest after depth label front discarded results
        last hf hi hc pcBound fetched lookup height arity types empty typed' slots')
      intro out effect
      obtain ⟨success, exactState, represented, sameStore, samePlatform, simulation⟩ := effect
      refine ⟨success, sameStore, samePlatform, target.target,
        { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results },
        targets.drop (depth + 1), targetNext, targetOutput, false, ?_, represented,
        .ready targetPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .branch _ depth label lookup _, ?_,uniform _ _,ownership,.branch {f with code := .BR (.mk_uN depth)::after} depth label lookup _⟩
      · rw [exactState]
      · apply ConcreteSim.of_source
        simpa only [← split] using simulation
    · have fetched : compiled.code.val[raw.pc.val]? = some (transferInstruction dst src count) := by
        simpa only [Nat.add_zero] using fragment.fetch
          (index := 0) (by simp only [Compiler.branchInstructions, if_neg noCopy, List.getElem?_cons_zero])
      have jump : compiled.code.val[raw.pc.val + 1]? = some (.Jump target.target) := by
        exact fragment.fetch (index := 1)
          (by simp only [Compiler.branchInstructions, if_neg noCopy, List.getElem?_cons_succ, List.getElem?_cons_zero])
      apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
        (transferInstruction dst src count) last hf hi hc fetched pcBound
      intro pc hpc
      apply WP.spec_mono (dispatch_branch_transfer_refines memory hooks floats allocator
        { exec with frames := exec.frames.set index { raw with pc := pc } }
        store platform index raw dst src count s ambient f rest after depth label front discarded results
        lookup height arity types typed' slots' destination source size capacity')
      intro out effect
      obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
      refine ⟨success, sameStore, samePlatform, pc,
        { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results },
        targets.drop (depth + 1), targetNext, targetOutput, true, unchanged, represented,
        .jump target.target (by simpa only [hpc] using jump) targetPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .branch _ depth label lookup _, ?_,uniform _ _,ownership,.branch {f with code := .BR (.mk_uN depth)::after} depth label lookup _⟩
      apply ConcreteSim.of_source
      simpa only [← split] using simulation

end Itasca.Runtime.Interp.Machine

end

/-! ## If -/

section

/-!
Execution of a structured if instruction.

Main declarations: `step_if`. A direct consumer is `Interp.Machine.Control.ControlExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem step_if {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (bt : blocktype) (yes no after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := .IFELSE bt yes no :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := .IFELSE bt yes no :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (targets' : List Compiler.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := .IFELSE bt yes no :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .IFELSE bt yes no :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        (g = {f with code := .IFELSE bt yes no :: after} ∨ SourceMachine.Core.step ⟨s,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩ = .next ⟨s,ambient,g::rest,[]⟩) ⦄ := by
  rcases code_rel_if_inv point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := .IFELSE bt yes no :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .IFELSE bt yes no :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨front, params, results, cond, noEntry, yesExit, exit, yesNormal, yesBranch, noNormal, noBranch, shape, signature, condition,
      fetched, yesCode, skipCode, noCode, continuation, bounds⟩ := branch
    have frameTyped : SourceMachine.FrameTyped s { f with code := .IFELSE bt yes no :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨values, bits, valueSplit, valueTypes, bitsBound⟩ := frame_integer_suffix frameTyped (front ++ params) .I32 shape
    have valueSplit : f.vals = values ++ [SourceMachine.integerVal .I32 bits] := valueSplit
    have frameTyped' : SourceMachine.FrameTyped s
        { f with code := .IFELSE bt yes no :: after, vals := values ++ [SourceMachine.integerVal .I32 bits] } [] := by
      simpa only [← valueSplit] using frameTyped
    have frameAfter := SourceMachine.if_frame_preservation frameTyped'
    have typedAfter := SourceMachine.active_frame_preservation typed.typed frameAfter rfl
    have labelsAfter : LabelsMatch values f.labels targets := by
      have old : LabelsMatch (values ++ [SourceMachine.integerVal .I32 bits]) f.labels targets := by
        simpa only [← valueSplit] using point.labels
      have h := old.replace_suffix (after := []) (SourceMachine.frame_typed_heights frameAfter)
      simpa only [List.append_nil] using h
    have position : cond.val = Compiler.slots ((f.locals ++ values).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append, Compiler.slots_append, valueTypes] using condition
    have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ values) ++ [SourceMachine.integerVal .I32 bits]) := by
      simpa only [FrameSlots, valueSplit, List.append_assoc] using slots
    have input : WordsAt exec.slots.val (raw.base.val + cond.val) [bits] := by
      simpa only [position, ValuesAt, Compiler.encodeValues, List.flatMap_cons, List.flatMap_nil,
        SourceMachine.integerVal, Compiler.encodeValue, List.append_nil] using allValues.operands
    have simulation : SourceMachine.NextSim
        ⟨s, ambient, { f with code := .IFELSE bt yes no :: after } :: rest, []⟩
        ⟨s, ambient, { f with code := .BLOCK bt (if bits = 0 then no else yes) :: after, vals := values } :: rest, []⟩ := by
      obtain ⟨wf, labels, vals, code⟩ := SourceMachine.frame_typed_wf frameTyped'
      have remaining : Forall SourceMachine.FrameWf rest := by
        cases typed.typed.frames with | cons _ h => exact SourceMachine.frames_typed_wf h
      have valuesWf : Forall wf_val values := fun value member => vals value (List.mem_append_left _ member)
      have step := SourceMachine.if_simulation s ambient f rest after values bits bt yes no typed.typed.store typed.typed.ambient
        wf labels valuesWf (fun i hi => code i (by simp [hi])) remaining
        (SourceMachine.frame_typed_heights frameAfter) bitsBound (code _ (by simp))
      apply SourceMachine.NextSim.single
      simpa only [← valueSplit] using step
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.JumpIfZero cond noEntry) last hf hi hc fetched pcBound
    intro pc hpc
    have valid : index.val < exec.frames.val.length := List.getElem?_eq_some_iff.mp hf |>.1
    have lookup : (exec.frames.set index { raw with pc := pc }).val[index.val]? = some { raw with pc := pc } := by
      simp [alloc.vec.Vec.set_val_eq, valid]
    apply WP.spec_mono (dispatch_jump_if_zero_exact memory hooks floats allocator
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index
      { raw with pc := pc } cond noEntry bits lookup bitsBound input)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    have selected : out.2.1 =
        { exec with frames := exec.frames.set index { raw with pc := if bits = 0 then noEntry else pc } } := by
      by_cases zero : bits = 0
      · simpa only [if_pos zero, frame_set_twice] using exactState
      · simpa only [if_neg zero] using exactState
    have selectedPoint : FramePoint s { raw with pc := if bits = 0 then noEntry else pc }
        { f with code := .BLOCK bt (if bits = 0 then no else yes) :: after, vals := values }
        compiled C targets next output := by
      refine ⟨point.bindings,point.locals,labelsAfter, ⟨?_, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
      by_cases zero : bits = 0
      · simp only [if_pos zero, valueTypes]
        exact Compiler.StructuredCode.ordinary_block signature noCode (fun live => continuation (Or.inr (Or.inr live))) ⟨bounds.2.1, bounds.2.2⟩
      · simp only [if_neg zero, valueTypes]
        apply Compiler.StructuredCode.if_then signature _ skipCode noCode.pc_le_next
          (fun live => continuation (live.elim Or.inl (fun h => Or.inr (Or.inl h))))
          ⟨by omega, bounds.2.2⟩
        simpa only [hpc] using yesCode
    refine ⟨success, sameStore, samePlatform, (if bits = 0 then noEntry else pc),
      { f with code := .BLOCK bt (if bits = 0 then no else yes) :: after, vals := values },
      targets, next, output, false, ?_, ?_, .ready selectedPoint, ⟨typedAfter,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_,Or.inr ?_⟩
    · rw [selected]
    · rw [selected]
      exact allValues.locals
    · simpa only [decide_eq_true_eq, ne_eq, ite_not] using SourceClosure.if_choice f bt yes no after (decide (bits ≠ 0)) values (values_references_prefix f values _ valueSplit)
    · apply ConcreteSim.of_source
      exact simulation
    · have accepts : SourceMachine.integer numtype.I32 (SourceMachine.integerVal .I32 bits) = some bits := by
        simpa only [numtype_Inn] using SourceMachine.integer_accepts .I32 bits bitsBound
      simp only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.astep,valueSplit,SourceMachine.pop_append,accepts,SourceMachine.advance]

end Itasca.Runtime.Interp.Machine

end

/-! ## Loop -/

section

/-!
Execution of a structured loop instruction.

Main declarations: `step_loop`. A direct consumer is `Interp.Machine.Control.ControlExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem step_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (bt : blocktype) (body after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := .LOOP bt body :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧
      ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (targets' : List Compiler.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := .LOOP bt body :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        (g = {f with code := .LOOP bt body :: after} ∨ SourceMachine.Core.step ⟨s,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩ = .next ⟨s,ambient,g::rest,[]⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate, out.2.2.2))) ⦄ := by
  rcases code_rel_loop_inv point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := .LOOP bt body :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨sameStore, Or.inl ⟨success, target, { f with code := .LOOP bt body :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl⟩⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨front, params, results, entry, exit, normalLive, shape, atEntry, signature, head, bodyCode, continuation, bounds⟩ := branch
    have sourceStep := loop_source_step s ambient f rest bt body after front params results (by simpa only [point.bindings.types] using signature) shape
    have typedNext := SourceMachine.loop_preservation s ambient f rest after bt body _ typed.typed sourceStep
    have simulation := SourceMachine.typed_loop_simulation s ambient f rest after bt body _ typed.typed sourceStep
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      .LoopHead last hf hi hc (by simpa only [atEntry] using head) pcBound
    intro pc hpc
    apply WP.spec_mono (dispatch_loop_head_effect memory hooks floats allocator law
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index raw)
    intro out effect
    obtain ⟨exactState, sameStore, decision, hook, result⟩ := effect
    refine ⟨sameStore, ?_⟩
    cases decision with
    | Terminate => exact Or.inr ⟨result, hook⟩
    | Continue =>
      refine Or.inl ⟨result, pc,
        { f with code := body, labels := ⟨params, results, [.LOOP bt body], front.length, after⟩ :: f.labels },
        ⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: targets,
        exit, front ++ results, false, ?_, ?_, .ready ?_, ⟨typedNext,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .loop _ _ _ _ _ _ _, ?_,Or.inr sourceStep⟩
      · rw [exactState]
      · rw [exactState]
        exact slots
      · refine ⟨point.bindings,point.locals,point.labels.enter front params results params entry exit [.LOOP bt body] after shape, ?_⟩
        simpa only [shape, hpc, atEntry] using Compiler.StructuredCode.Point.loop_body signature head bodyCode continuation bounds
          point.code.targets point.code.normal point.code.exit point.code.root
      · apply ConcreteSim.of_source
        exact simulation

end Itasca.Runtime.Interp.Machine

end

/-! ## ControlExecution -/

section

/-!
Structured control fetch and whole-execution preservation. Fetch inversion for if, loop and branches supplies the execution lemmas with their explicit uniform or concrete emission premises.
-/

/-! ## Control Fetch -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem loop_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame} [OrdinaryHeads (emission compiled)]
    (bt : blocktype) (body after : List instr)
    (point : FramePoint s raw {f with code := .LOOP bt body::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases code_rel_loop_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨front,params,results,entry,exit,live,shape,atEntry,signature,fetch,bodyCode,continuation,bounds⟩ := branch
    exact ⟨.LoopHead,by simpa only [atEntry] using fetch,.loopHead⟩

theorem if_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame} [OrdinaryHeads (emission compiled)]
    (bt : blocktype) (yes no after : List instr)
    (point : FramePoint s raw {f with code := .IFELSE bt yes no::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases code_rel_if_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨front,params,results,cond,noEntry,yesExit,exit,yn,yb,nn,nb,shape,signature,condition,fetch,yesCode,skip,noCode,continuation,bounds⟩ := branch
    exact ⟨_,fetch,.jumpZero cond noEntry⟩

theorem transfer_prefix (dst src count : U32) : PrefixInstruction (Compiler.transferInstruction dst src count) := by
  unfold Compiler.transferInstruction
  split
  · exact .copy ..
  · split
    · exact .copy2 ..
    · exact .copyN ..

theorem branch_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame} [OrdinaryHeads (emission compiled)]
    (depth : Nat) (after : List instr)
    (point : FramePoint s raw {f with code := .BR (.mk_uN depth)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases code_rel_branch_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨target,dst,src,count,finish,lookup,live,layout,fragment,remaining⟩ := branch
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · refine ⟨.Jump target.target,?_,.jump _⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Compiler.branchInstructions,if_pos noCopy,List.getElem?_cons_zero])
    · refine ⟨Compiler.transferInstruction dst src count,?_,transfer_prefix ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Compiler.branchInstructions,if_neg noCopy,List.getElem?_cons_zero])

theorem branch_if_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame} [OrdinaryHeads (emission compiled)]
    (depth : Nat) (after : List instr)
    (point : FramePoint s raw {f with code := .BR_IF (.mk_uN depth)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases code_rel_branch_if_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨before,target,dst,src,count,cond,resume,shape,lookup,live,layout,condition,fragment,continuation⟩ := branch
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · refine ⟨.JumpIfNonZero cond target.target,?_,.jumpNonzero ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Compiler.branchIfInstructions,if_pos noCopy,List.getElem?_cons_zero])
    · refine ⟨.JumpIfZero cond resume,?_,.jumpZero ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Compiler.branchIfInstructions,if_neg noCopy,List.getElem?_cons_zero])
end Itasca.Runtime.Interp.Machine

end

/-! ## Control Execution -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_if_execution_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (bt : blocktype) (yes no : List instr) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .IFELSE bt yes no :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := if_fetch bt yes no after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_if memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest bt yes no after last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,sourceStep⟩ := effect
  have uniform : UniformConcreteSim raw.pc.val pc.val false pending
      ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩
      ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
    rcases sourceStep with same | step
    · subst g
      exact simulation.uniform_same (by scalar_tac)
    · apply UniformConcreteSim.single
      apply SourceMachine.typed_if_positive _ _ _ _ _ _ _ _ _ machine.typed.typed
      simpa only [SourceMachine.Core.step, SourceMachine.Core.instruction] using step
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases sourceStep with same | step
    · rw [same]; exact machine.core
    · exact Machine.core_step_supported machine.typed machine.core step
  have ownership := Machine.owned_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
  have bounded := Machine.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,ownership,bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

theorem step_loop_execution_uniform     (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
(platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (bt : blocktype) (body : List instr) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .LOOP bt body :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate,out.2.2.2))) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := loop_fetch bt body after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_loop memory hooks floats allocator law exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest bt body after last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨storeSame,success | stopped⟩ := effect
  · obtain ⟨success,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,sourceStep⟩ := success
    have uniform : UniformConcreteSim raw.pc.val pc.val false pending
        ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩
        ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases sourceStep with same | step
      · subst g
        exact simulation.uniform_same (by scalar_tac)
      · apply UniformConcreteSim.single
        apply SourceMachine.typed_loop_positive _ _ _ _ _ _ _ _ machine.typed.typed
        simpa only [SourceMachine.Core.step, SourceMachine.Core.instruction] using step
    have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases sourceStep with same | step
      · rw [same]; exact machine.core
      · exact Machine.core_step_supported machine.typed machine.core step
    have ownership := Machine.owned_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
    have bounded := Machine.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
    refine ⟨storeSame,Or.inl ⟨success,pc,g,pending,?_,simulation,uniform,ownership,bounded⟩⟩
    exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
      represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered
  · exact ⟨storeSame,Or.inr stopped⟩

theorem step_loop_execution     (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
(platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (bt : blocktype) (body : List instr) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .LOOP bt body :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate,out.2.2.2))) ⦄ := by
  apply WP.spec_mono (step_loop_execution_uniform memory hooks floats allocator law platform frameIndex view code exec store raw inst compiled ambient f rest bt body after C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨storeSame,success | stopped⟩
  · rcases success with ⟨success,pc,g,pending,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨storeSame,Or.inl ⟨success,pc,g,pending,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨storeSame,Or.inr stopped⟩

theorem step_branch_execution_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (depth : Nat) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .BR (.mk_uN depth) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .BR (.mk_uN depth) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .BR (.mk_uN depth) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := branch_fetch depth after point
  have pcBound := program.fetched_bound instruction fetched
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]
    exact frameFound
  have binding := (machine.stack.top raw top).binding
  have capacity := slots.capacity binding
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_branch_owned_uniform memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest depth after last frameFound found codeFound pcBound machine.typed slots capacity point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,uniform,ownership,bounded⟩ := effect
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    exact Machine.SyntaxClosure.supported closure machine.core
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,fun _ h => FrameOwnershipClosure.stateful ownership h,fun _ h => bounded.state h⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

theorem step_branch_if_execution_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (depth : Nat) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .BR_IF (.mk_uN depth) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := branch_if_fetch depth after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_branch_if_owned_uniform memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest depth after (.br _) last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,uniform,ownership,bounded⟩ := effect
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    exact Machine.SyntaxClosure.supported closure machine.core
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,fun _ h => FrameOwnershipClosure.stateful ownership h,fun _ h => bounded.state h⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

end Itasca.Runtime.Interp.Machine

end

end
