import Exec.Interp.Core.BoundClosure
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.FloatCore.BranchInversion
import Exec.Interp.FloatCore.BranchPoint
import Exec.Interp.FloatCore.SyntaxClosure
import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Interp.FloatCore.SuspendedPoint
import Exec.Abs.Core.Typing
import Exec.Interp.Control.BranchNoCopy

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A complete BR iteration, including compiler-elided copies and forward
administrative skips. All operand decomposition, slots and target continuation
come from retained structured code evidence and generated source typing. -/
theorem step_branch_float_core_owned {M P F A : Type}
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
    (typed : Abs.CoreTyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) ≤ exec.slots.length)
    (point : FloatFramePoint s raw { f with code := .BR (.mk_uN depth) :: after }
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
        FloatCoreSyntaxClosure { f with code := .BR (.mk_uN depth) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        FrameOwnershipClosure {f with code := .BR (.mk_uN depth) :: after} g ∧
        FrameBoundClosure {f with code := .BR (.mk_uN depth) :: after} g ⦄ := by
  rcases floatCoreCodeRel_branch_inv point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FloatFramePoint s { raw with pc := target }
        { f with code := .BR (.mk_uN depth) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .BR (.mk_uN depth) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,.refl _,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨target, dst, src, count, fragmentEnd, staticLookup, live, layout, fragment, remaining⟩ := branch
    obtain ⟨label, front, discarded, results, lookup, matching, split, height, arity, types,
      destination, source, size⟩ := point.labels.branchLayout f.locals depth target staticLookup dst src count (by simpa only [point.locals] using layout)
    have frameTyped : Abs.FrameTyped s { f with code := .BR (.mk_uN depth) :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    have point' : FloatFramePoint s raw { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results }
        compiled C targets next output := by simpa only [← split] using point
    have typed' : Abs.ATyped ⟨s, ambient,
        { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩ := by
      simpa only [← split] using typed.typed
    have slots' : FrameSlots exec raw { f with vals := front ++ discarded ++ results } := by simpa only [← split] using slots
    have capacity' : raw.base.val + Code.slots ((f.locals ++ front ++ discarded ++ results).map Code.valueType) ≤ exec.slots.length := by
      have valuesSplit : f.vals = front ++ discarded ++ results := split
      simpa only [valuesSplit, List.append_assoc] using capacity
    obtain ⟨actual, targetNext, targetOutput, actualAt, _, targetPoint⟩ := point'.branch front discarded results
      (by simpa only [← split] using frameTyped) depth label lookup height types
      (by intro found lookup; have same : found = target := Option.some.inj (lookup.symm.trans staticLookup); subst found; exact live)
    have same : actual = target := Option.some.inj (actualAt.symm.trans staticLookup)
    subst actual
    have sourceStep := branch_source_step s ambient f rest after depth label front discarded results lookup height arity types
    have nextTyped := Abs.instruction_preservation s ambient { f with vals := front ++ discarded ++ results } rest
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
          (index := 0) (by simp only [Code.branchInstructions, if_pos noCopy, List.getElem?_cons_zero])
      have empty := branch_no_transfer destination source size noCopy
      apply WP.spec_mono (step_branchNoCopy_refines memory hooks floats allocator exec store platform
        index raw target.target inst compiled s ambient f rest after depth label front discarded results
        last hf hi hc pcBound fetched lookup height arity types empty typed' slots')
      intro out effect
      obtain ⟨success, exactState, represented, sameStore, samePlatform, simulation⟩ := effect
      refine ⟨success, sameStore, samePlatform, target.target,
        { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results },
        targets.drop (depth + 1), targetNext, targetOutput, false, ?_, represented,
        .ready targetPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .branch _ depth label lookup _, ?_,ownership,.branch {f with code := .BR (.mk_uN depth)::after} depth label lookup _⟩
      · rw [exactState]
      · apply ConcreteSim.of_source
        simpa only [← split] using simulation
    · have fetched : compiled.code.val[raw.pc.val]? = some (transferInstruction dst src count) := by
        simpa only [Nat.add_zero] using fragment.fetch
          (index := 0) (by simp only [Code.branchInstructions, if_neg noCopy, List.getElem?_cons_zero])
      have jump : compiled.code.val[raw.pc.val + 1]? = some (.Jump target.target) := by
        exact fragment.fetch (index := 1)
          (by simp only [Code.branchInstructions, if_neg noCopy, List.getElem?_cons_succ, List.getElem?_cons_zero])
      apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
        (transferInstruction dst src count) last hf hi hc fetched pcBound
      intro pc hpc
      apply WP.spec_mono (dispatch_branchTransfer_refines memory hooks floats allocator
        { exec with frames := exec.frames.set index { raw with pc := pc } }
        store platform index raw dst src count s ambient f rest after depth label front discarded results
        lookup height arity types typed' slots' destination source size capacity')
      intro out effect
      obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
      refine ⟨success, sameStore, samePlatform, pc,
        { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results },
        targets.drop (depth + 1), targetNext, targetOutput, true, unchanged, represented,
        .jump target.target (by simpa only [hpc] using jump) targetPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .branch _ depth label lookup _, ?_,ownership,.branch {f with code := .BR (.mk_uN depth)::after} depth label lookup _⟩
      apply ConcreteSim.of_source
      simpa only [← split] using simulation

end Exec.Interp
