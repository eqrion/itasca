import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Control.ControlInversion
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Control.BranchConditionStep
import Itasca.Runtime.Interp.Relations.TypedOperands

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
