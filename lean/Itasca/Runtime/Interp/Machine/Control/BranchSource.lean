import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Compiler.Local.Lowering.Float.SafetyAndEncoding
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTable
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.SourceMachine.TransitionAndHostPreparation
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.SourceMachine.Core.ProgressAndBounds
import Itasca.Runtime.Interp.Control.NormalizeCompose

/-!
Proofs for Runtime / Interp / Machine / Control.

This module collects BranchPoint, BranchSource.
Each section documents its contracts and consumers.
-/

/-! ## BranchPoint -/

section

open Itasca.Representation

/-! ## ForwardJump -/

section

/-!
A retained forward jump is a source stutter with a strictly decreasing administrative measure. It preserves all slot words and mutable store data.

Main declarations: `step_forward_jump_flat`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

/-- A retained forward jump is a source stutter with a strictly decreasing
administrative measure. It preserves all slot words and mutable store data. -/
theorem step_forward_jump_flat {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (target : U32)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (forward : raw.pc.val < target.val)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Jump target))
    (slots : FrameSlots exec raw f)
    (point : FramePoint sourceStore {raw with pc := target} f compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,f::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      out.2.1 = {exec with frames := exec.frames.set index {raw with pc := target}} ∧
      FrameSlots out.2.1 {raw with pc := target} f ∧
      FramePoint sourceStore {raw with pc := target} f compiled C targets next output ∧
      SourceMachine.CoreTyped ⟨sourceStore,ambient,f::rest,[]⟩ ∧
      ConcreteSim compiled.code.length raw.pc.val target.val false false
        ⟨sourceStore,ambient,f::rest,[]⟩ ⟨sourceStore,ambient,f::rest,[]⟩ ⦄ := by
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform index raw inst compiled target
    last frameFound instanceFound codeFound pcBound fetched)
  intro out effect
  obtain ⟨success,exactState,sameStore,samePlatform⟩ := effect
  refine ⟨success,sameStore,samePlatform,exactState,?_,point,typed,?_⟩
  · simpa only [exactState,FrameSlots] using slots
  · exact Or.inl ⟨rfl,dispatch_measure_forward _ _ _ _ forward point.code.current.entry_bound⟩
end Itasca.Interp.Machine

end

/-! ## ControlInversion -/

section

/-!
Inversion of block, loop and if code relations.

Main declarations: `code_rel_block_inv` and `code_rel_if_inv`.
-/

namespace Itasca.Interp.Machine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem code_rel_block_inv {C returns code labels stack pc next output bt body after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.BLOCK bt body :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.BLOCK bt body :: after) target.val next output) ∨
    (∃ front params results normalExit branchExit normalLive branchLive,
      stack = front ++ params ∧ Compiler.BlockSignature C.TYPES bt params results ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables
        (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
        (front ++ params) body pc normalExit (front ++ results) ∧
      (normalLive = true → Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels (front ++ results) after normalExit next output) ∧
      (branchLive = true → Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels (front ++ results) after branchExit.val next output) ∧
      pc ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_block head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | block signature bodyCode rest targetRest bounds => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, signature, bodyCode, rest, targetRest, bounds⟩

theorem code_rel_loop_inv {C returns code labels stack pc next output bt body after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.LOOP bt body :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.LOOP bt body :: after) target.val next output) ∨
    (∃ front params results entry exit normalLive,
      stack = front ++ params ∧ pc = entry.val ∧ Compiler.BlockSignature C.TYPES bt params results ∧
      code[entry.val]? = some .LoopHead ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables
        (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
        (front ++ params) body (entry.val + 1) exit (front ++ results) ∧
      (normalLive = true → Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels (front ++ results) after exit next output) ∧
      entry.val ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_loop head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | loop signature head bodyCode rest bounds => exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl, signature, head, bodyCode, rest, bounds⟩

theorem code_rel_if_inv {C returns code labels stack pc next output bt yes no after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.IFELSE bt yes no :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.IFELSE bt yes no :: after) target.val next output) ∨
    (∃ front params results cond noEntry yesExit exit yesNormal yesBranch noNormal noBranch,
      stack = front ++ params ++ [.I32] ∧ Compiler.BlockSignature C.TYPES bt params results ∧
      cond.val = Representation.slots C.LOCALS + Representation.slots (front ++ params) ∧
      code[pc]? = some (.JumpIfZero cond noEntry) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables
        (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
        (front ++ params) yes (pc + 1) yesExit (front ++ results) ∧
      Compiler.IfSkip code yesExit noEntry exit yesNormal ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables
        (⟨front, results, results, exit, exit.val, [], after, noNormal, noBranch⟩ :: labels)
        (front ++ params) no noEntry.val exit.val (front ++ results) ∧
      (yesNormal = true ∨ yesBranch = true ∨ noNormal = true ∨ noBranch = true →
        Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels (front ++ results) after exit.val next output) ∧
      pc + 1 ≤ next ∧ noEntry.val ≤ next ∧ next ≤ code.length) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | ifElse signature condition guard yesCode skip noCode rest bounds =>
    exact Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, signature, condition, guard, yesCode, skip, noCode, rest, bounds⟩

end Itasca.Interp.Machine

end

/-! ## LabelCompletion -/

section

/-!
Normal completion removes a source label at its retained fallthrough PC. The concrete words and PC are unchanged; the generated source semantics takes one positive reduction and installs the retained enclosing continuation.

Main declarations: `label_completion_point`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std
/-- Normal completion removes a source label at its retained fallthrough PC.
The concrete words and PC are unchanged; the generated source semantics takes
one positive reduction and installs the retained enclosing continuation. -/
theorem label_completion_point (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (label : SourceMachine.Label) (labels : List SourceMachine.Label)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := [], labels := label :: labels }
      compiled C targets next output)
    (atExit : raw.pc.val = next) (live : Compiler.NormalLive targets) :
    ∃ next' output',
      FrameSlots exec raw { f with code := label.after, labels := labels } ∧
      FramePoint s raw { f with code := label.after, labels := labels }
        compiled C (targets.drop 1) next' output' ∧
      SourceMachine.ATyped ⟨s, ambient, { f with code := label.after, labels := labels } :: rest, []⟩ ∧
      SourceMachine.NextSim ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩
        ⟨s, ambient, { f with code := label.after, labels := labels } :: rest, []⟩ := by
  have frameTyped : SourceMachine.FrameTyped s { f with code := [], labels := label :: labels } [] := by
    cases typed.frames with | cons h _ => exact h
  obtain ⟨size, results, step⟩ := typed_label_completion s ambient f rest label labels frameTyped
  obtain ⟨target, lookup, matching⟩ := point.labels.atIndex 0 label (by rfl)
  have head : targets.head? = some target := by cases targets <;> simpa using lookup
  have pc : raw.pc.val = target.normalExit := atExit.trans (point.code.exit target head)
  obtain ⟨next', output', relation, aligned, root⟩ := point.code.normal 0 target lookup (live target head)
  have valueTypes : f.vals.map Representation.valueType = target.front ++ target.resultTypes := by
    rw [matching.front, matching.resultTypes]
    have resultTypes : (f.vals.drop label.height).map Representation.valueType = label.resultTypes := by
      simpa only [show Representation.valueType = SourceMachine.valueType from funext value_type_eq_abs] using results
    rw [← resultTypes, ← List.map_append, List.take_append_drop]
  refine ⟨next', output', slots, ⟨point.bindings,point.locals,?_, ?_⟩, ?_, ?_⟩
  · simpa only [List.drop_succ_cons, List.drop_zero] using point.labels.drop 1
  · exact ⟨by simpa only [Nat.zero_add, matching.after, pc, valueTypes] using relation,
      point.code.targets.drop 1, point.code.normal.drop 1, by simpa only [Nat.zero_add] using aligned, by simpa only [Nat.zero_add] using root⟩
  · exact SourceMachine.active_frame_preservation typed (SourceMachine.label_exit_frame_preservation frameTyped) rfl
  · exact SourceMachine.typed_label_end_simulation s ambient f rest label labels _ typed step

end Itasca.Interp.Machine

end

/-! ## BranchInversion -/

section

/-!
Inversion of direct and conditional branch code relations.

Main declarations: `code_rel_branch_inv` and `code_rel_branch_if_inv`.
-/

namespace Itasca.Interp.Machine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem code_rel_branch_inv {C returns code labels stack pc next output depth after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.BR (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.BR (.mk_uN depth) :: after) target.val next output) ∨
    (∃ label dst src count fragmentEnd,
      labels[depth]? = some label ∧ label.branchLive = true ∧ Compiler.BranchLayout C.LOCALS stack label dst src count ∧
      Compiler.Segment code pc (Compiler.branchInstructions dst src count label.target) fragmentEnd ∧ fragmentEnd ≤ next) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_br head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branch lookup live layout fragment remaining scope => exact Or.inr ⟨_, _, _, _, _, lookup, live, layout, fragment, remaining⟩

theorem code_rel_branch_if_inv {C returns code labels stack pc next output depth after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.BR_IF (.mk_uN depth) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack (.BR_IF (.mk_uN depth) :: after) target.val next output) ∨
    (∃ before label dst src count cond resume,
      stack = before ++ [.I32] ∧ labels[depth]? = some label ∧ label.branchLive = true ∧
      Compiler.BranchLayout C.LOCALS before label dst src count ∧ cond.val = Representation.slots C.LOCALS + Representation.slots before ∧
      Compiler.Segment code pc (Compiler.branchIfInstructions dst src count label.target cond resume) resume.val ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels before after resume.val next output) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_br_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branchIf lookup live layout condition fragment rest => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, lookup, live, layout, condition, fragment, rest⟩

end Itasca.Interp.Machine

end

/-! ## BranchPoint -/

section

/-!
Target lookup exposes the retained source continuation, with concrete label fields obtained from the dynamic/static label correspondence.

Main declarations: `FramePoint.target` and `branch_target_point`.
-/

namespace Itasca.Interp.Machine
open Aeneas.Std
/-- Target lookup exposes the retained source continuation, with concrete
label fields obtained from the dynamic/static label correspondence. -/
theorem FramePoint.target {s raw frame compiled C targets next output}
    (point : FramePoint s raw frame compiled C targets next output)
    (depth : Nat) (label : SourceMachine.Label) (lookup : frame.labels[depth]? = some label)
    (live : ∀ target, targets[depth]? = some target → target.branchLive = true) :
    ∃ target targetNext targetOutput,
      targets[depth]? = some target ∧ LabelMatch frame.vals label target ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS frame.resultTypes
        C.LOCALS compiled.code.val compiled.jump_tables.val (targets.drop (depth + 1))
        (target.front ++ label.branchTypes) (label.cont ++ label.after)
        target.target.val targetNext targetOutput := by
  obtain ⟨target, found, matching⟩ := point.labels.atIndex depth label lookup
  obtain ⟨targetNext, targetOutput, continuation, aligned, root⟩ := point.code.targets depth target found (live target found)
  refine ⟨target, targetNext, targetOutput, found, matching, ?_⟩
  exact ⟨by simpa only [matching.branchTypes, matching.cont, matching.after] using continuation,
    point.code.targets.drop (depth + 1), point.code.normal.drop (depth + 1), aligned, root⟩

/-- A typed source branch preserves the surviving dynamic/static label
correspondence and installs the exact retained target continuation. -/
theorem FramePoint.branch {s : _root_.store} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {compiled : runtime.bytecode.CompiledFunction}
    {C : context} {targets : List Compiler.LabelTarget} {next : Nat} {output : List valtype}
    (front discarded results : List val)
    (point : FramePoint s raw { f with vals := front ++ discarded ++ results } compiled C targets next output)
    (typed : SourceMachine.FrameTyped s { f with vals := front ++ discarded ++ results } [])
    (depth : Nat) (label : SourceMachine.Label) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (types : results.map SourceMachine.valueType = label.branchTypes)
    (live : ∀ target, targets[depth]? = some target → target.branchLive = true) :
    ∃ target targetNext targetOutput,
      targets[depth]? = some target ∧ LabelMatch (front ++ discarded ++ results) label target ∧
      FramePoint s { raw with pc := target.target }
        { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results }
        compiled C (targets.drop (depth + 1)) targetNext targetOutput := by
  obtain ⟨target, targetNext, targetOutput, found, matching, continuation⟩ := point.target depth label lookup live
  have frontTypes : target.front = front.map Representation.valueType := by
    simpa only [height, List.append_assoc, List.take_left] using matching.front
  have resultTypes : results.map Representation.valueType = label.branchTypes := by
    simpa only [show Representation.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types
  have outer := typed.outer_heights depth label lookup
  have labels := point.labels.branch depth (by simpa only [height] using outer)
  refine ⟨target, targetNext, targetOutput, found, matching, ⟨point.bindings,point.locals,labels, ?_⟩⟩
  simpa only [List.map_append, resultTypes, frontTypes] using continuation

theorem branch_target_point {s : _root_.store} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {compiled : runtime.bytecode.CompiledFunction}
    {C : context} {targets : List Compiler.LabelTarget}
    (front discarded results : List val)
    (bindings : SourceMachine.ModuleBindings s f.module C) (locals : C.LOCALS = f.locals.map Representation.valueType)
    (matchingLabels : LabelsMatch (front ++ discarded ++ results) f.labels targets)
    (continuations : Compiler.StructuredCode.Targets (emission compiled C) C.TYPES C.FUNCS f.resultTypes
      C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (normal : Compiler.StructuredCode.Normals (emission compiled C) C.TYPES C.FUNCS f.resultTypes
      C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (typed : SourceMachine.FrameTyped s { f with vals := front ++ discarded ++ results } [])
    (depth : Nat) (label : SourceMachine.Label) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (types : results.map SourceMachine.valueType = label.branchTypes)
    (live : ∀ target, targets[depth]? = some target → target.branchLive = true) :
    ∃ target targetNext targetOutput,
      targets[depth]? = some target ∧ LabelMatch (front ++ discarded ++ results) label target ∧
      FramePoint s { raw with pc := target.target }
        { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results }
        compiled C (targets.drop (depth + 1)) targetNext targetOutput := by
  obtain ⟨target, found, matching⟩ := matchingLabels.atIndex depth label lookup
  obtain ⟨targetNext, targetOutput, relation, aligned, root⟩ := continuations depth target found (live target found)
  have continuation : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes
      C.LOCALS compiled.code.val compiled.jump_tables.val (targets.drop (depth + 1))
      (target.front ++ label.branchTypes) (label.cont ++ label.after) target.target.val targetNext targetOutput :=
    ⟨by simpa only [matching.branchTypes, matching.cont, matching.after] using relation,
      continuations.drop (depth + 1), normal.drop (depth + 1), aligned, root⟩
  have frontTypes : target.front = front.map Representation.valueType := by
    simpa only [height, List.append_assoc, List.take_left] using matching.front
  have resultTypes : results.map Representation.valueType = label.branchTypes := by
    simpa only [show Representation.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types
  have outer := typed.outer_heights depth label lookup
  have labels := matchingLabels.branch depth (by simpa only [height] using outer)
  refine ⟨target, targetNext, targetOutput, found, matching, ⟨bindings,locals,labels, ?_⟩⟩
  simpa only [List.map_append, resultTypes, frontTypes] using continuation

end Itasca.Interp.Machine

end

end

/-! ## BranchSource -/

section

open Itasca.Representation

/-! ## BranchTable -/

section

/-!
Branch-table lookup and execution. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Branch Table Point -/

section

namespace Itasca.Interp.Machine
open Aeneas.Std

theorem branch_table_point_head {emit types functions returns locals code jumpTables labels stack pc next output depths fallback after}
    (point : Compiler.StructuredCode.Point emit types functions returns locals code jumpTables labels stack
      (.BR_TABLE depths fallback::after) pc next output) :
    (∃ target : U32, pc<target.val ∧ code[pc]?=some (.Jump target) ∧
      Compiler.StructuredCode.Point emit types functions returns locals code jumpTables labels stack
        (.BR_TABLE depths fallback::after) target.val next output) ∨
    (∃ front selector start len, stack=front++[.I32] ∧
      Compiler.BranchTableLayout jumpTables locals labels front code depths fallback pc next selector start len) := by
  cases point.current with
  | linear head ordinary fragment rest => exact False.elim (ordinary depths fallback rfl)
  | skip forward fetched rest =>
    exact Or.inl ⟨_,forward,fetched,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | branchTable gate table bounds => exact Or.inr ⟨_,_,_,_,rfl,table⟩

end Itasca.Interp.Machine
namespace Itasca.Compiler
open Aeneas.Std

theorem BranchTableEntry.structured_indexed {locals labels stack code depth entry next}
    (entryCode : BranchTableEntry locals labels stack code depth entry next)
    (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns : List valtype) (jumpTables : List U32)
    (after : List instr) (output : List valtype) :
    StructuredCode emission types functions returns locals code jumpTables labels stack
      (.BR depth :: after) entry.val next output := by
  obtain ⟨label,dst,src,count,fragmentEnd,lookup,live,layout,fragment,remaining,scope⟩ := entryCode
  cases depth with
  | mk_uN depth => exact .branch lookup live layout fragment remaining scope
end Itasca.Compiler

end

/-! ## Branch Table -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

/-- The side-table certificate selects an ordinary structured BR point. No
per-target execution assumption is retained: every target is an exact emitted
branch fragment with the existing scope continuation evidence. -/
theorem step_br_table_point {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (selector start len : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depths : List labelidx) (fallback : labelidx) (front : List val)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (instanceLookup : store.instances.val[raw.instance.val]? = some inst)
    (functionLookup : inst.module.functions.val[raw.function.val]? = some compiled)
    (last : frameIndex.val+1 = exec.frames.length) (pcBound : raw.pc.val < U32.max)
    (bound : value < 2^32)
    (table : Compiler.BranchTableCode (Compiler.CompilerTables.ofFunction compiled) C.LOCALS targets
      (front.map Representation.valueType) compiled.code.val depths fallback raw.pc.val next selector start len)
    (bindings : SourceMachine.ModuleBindings s f.module C) (locals : C.LOCALS = f.locals.map Representation.valueType)
    (labels : LabelsMatch (front ++ [SourceMachine.integerVal .I32 value]) f.labels targets)
    (continuations : Compiler.StructuredCode.Targets (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (normals : Compiler.StructuredCode.Normals (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (aligned : Compiler.ExitAligned targets next) (root : Compiler.RootAligned compiled.code.val f.resultTypes targets next output)
    (typed : SourceMachine.CoreTyped ⟨s,ambient,{f with code := .BR_TABLE depths fallback::after,vals := front ++ [SourceMachine.integerVal .I32 value]}::rest,[]⟩)
    (slots : FrameSlots exec raw {f with vals := front ++ [SourceMachine.integerVal .I32 value]}) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ∃ target, out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := target}} ∧
      FrameSlots out.2.1 {raw with pc := target} {f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front} ∧
      FramePoint s {raw with pc := target} {f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front}
        compiled C targets next output ∧
      SourceMachine.CoreTyped ⟨s,ambient,{f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front}::rest,[]⟩ ∧
      SourceMachine.NextSim ⟨s,ambient,{f with code := .BR_TABLE depths fallback::after,vals := front ++ [SourceMachine.integerVal .I32 value]}::rest,[]⟩
        ⟨s,ambient,{f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front}::rest,[]⟩ ⦄ := by
  obtain ⟨target,lookup,entry⟩ := table.selected value
  have frameTyped : SourceMachine.FrameTyped s {f with code := .BR_TABLE depths fallback::after,vals := front ++ [SourceMachine.integerVal .I32 value]} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  have heights : ∀ label ∈ f.labels, label.height ≤ front.length := by
    obtain ⟨C,first,operands,ins,outs,bindings,locals,head,split,operandTypes,firstWf,bounds⟩ :=
      SourceMachine.frame_typed_operands_bounds (f := {f with vals := front ++ [SourceMachine.integerVal .I32 value]}) frameTyped
    cases head with
    | br_table =>
      have sizes := congrArg List.length split
      have operandSizes := operandTypes.length_eq
      simp only [List.length_append,List.length_singleton] at sizes operandSizes
      intro label member
      have small := bounds label member
      omega
  have reducedLabels : LabelsMatch front f.labels targets := by
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  have point : FramePoint s {raw with pc := target}
      {f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front} compiled C targets next output := by
    exact ⟨bindings,locals,reducedLabels,
      ⟨entry.structured_indexed (emission compiled C) C.TYPES C.FUNCS f.resultTypes compiled.jump_tables.val after output,
        continuations,normals,aligned,root⟩⟩
  apply WP.spec_mono (step_br_table_refines memory hooks floats allocator exec store platform frameIndex raw inst compiled
    selector start len target value s ambient f rest after depths fallback front frameLookup instanceLookup functionLookup
    last pcBound table.instruction bound table.length table.arithmetic
    (by simpa only [table.length,Nat.add_sub_cancel,Compiler.CompilerTables.ofFunction] using lookup)
    (by simpa only [locals,List.map_append,Representation.slots_append] using table.selectorSlot) typed.typed slots)
  rintro out ⟨success,exactState,sameStore,samePlatform,outputSlots,afterTyped,simulation⟩
  exact ⟨target,success,sameStore,samePlatform,exactState,outputSlots,point,⟨afterTyped,typed.contents⟩,simulation⟩
end Itasca.Interp.Machine

end

/-! ## Branch Table Execution -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

/-- The actual table jump consumes its selector, then reuses the checked branch
fragment inside the same active and suspended machine. -/
theorem step_br_table_execution
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depths : List labelidx) (fallback : labelidx) (front : List val) (value : Nat)
    (selector start len : U32) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Representation.decodeStore view code store) raw
      {f with code:=.BR_TABLE depths fallback::after} compiled C targets next output)
    (values : f.vals=front++[SourceMachine.integerVal .I32 value]) (bound : value<2^32)
    (table : Compiler.BranchTableCode (Compiler.CompilerTables.ofFunction compiled) C.LOCALS targets
      (front.map Representation.valueType) compiled.code.val depths fallback raw.pc.val next selector start len)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ expected raw.pc.val false) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.1=store ∧ out.2.2.2=platform ∧
      Advance view code store out.2.1 expected compiled.code.length raw.pc.val false
        ⟨Representation.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ ⦄ := by
  have transition : SourceMachine.BrTable.Transition
      ⟨Representation.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩
      ⟨Representation.decodeStore view code store,ambient,{f with code:=.BR (SourceMachine.BrTable.select depths fallback value)::after,vals:=front}::rest,[]⟩ := .next values bound
  apply WP.spec_mono (step_br_table_point memory hooks floats allocator exec store platform index raw inst compiled selector start len value
    (Representation.decodeStore view code store) ambient f rest after depths fallback front C targets next output hf hi hc last
    (program.fetched_bound _ table.instruction) bound table point.bindings point.locals
    (by simpa only [←values] using point.labels) point.code.targets point.code.normal point.code.exit point.code.root
    (by simpa only [←values] using machine.typed) (by simpa only [←values] using slots))
  rintro out ⟨target,success,sameStore,samePlatform,effect,represented,retained,typed,simulation⟩
  refine ⟨success,sameStore,samePlatform,target.val,false,
    ⟨Representation.decodeStore view code store,ambient,{f with code:=.BR (SourceMachine.BrTable.select depths fallback value)::after,vals:=front}::rest,[]⟩,?_,?_,?_,rfl,?_⟩
  · exact Execution.ordinary view code ambient {f with code:=.BR_TABLE depths fallback::after}
      {f with code:=.BR (SourceMachine.BrTable.select depths fallback value)::after,vals:=front} rest expected raw.pc.val false machine
      (.refl store) (Itasca.Spec.extend_store_refl _ machine.typed.typed.store) raw index target last hf program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ (by rw [effect]) (by rw [effect]; exact .refl _ _) typed
      (transition.next_supported machine.core)
  · exact ConcreteSim.of_source _ _ _ _ _ (transition.correct machine.typed).2
  · exact fun _ owned => transition.next_owned owned
  · exact fun _ bounded => transition.next_bound bounded
end Itasca.Interp.Machine

end

end

/-! ## JumpExecution -/

section

/-!
Execution of a forward bytecode jump.

Main declarations: `step_forward_jump`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std SpecExt Itasca.Spec

theorem step_forward_jump
    {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (expected : List valtype)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype) (target : U32)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (forward : raw.pc.val<target.val) (fetch : compiled.code.val[raw.pc.val]?=some (.Jump target))
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Representation.decodeStore view code store) {raw with pc:=target} f compiled C targets next output)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.1=store ∧ out.2.2.2=platform ∧
      out.2.1={exec with frames:=exec.frames.set index {raw with pc:=target}} ∧
      Execution view code store out.2.1 ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ expected target.val false ∧
      ConcreteSim compiled.code.length raw.pc.val target.val false false
        ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ ⦄ := by
  have pcBound : raw.pc.val<U32.max := by
    have inside := (List.getElem?_eq_some_iff.mp fetch).1
    have bound := program.fetchBound
    omega
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform index raw inst compiled target last frameFound found codeFound pcBound fetch)
  intro out effect
  obtain ⟨success,exactState,sameStore,samePlatform⟩ := effect
  refine ⟨success,sameStore,samePlatform,exactState,?_,?_⟩
  · apply Execution.ordinary view code ambient f f rest expected raw.pc.val false machine (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw index target last frameFound program (.ready point)
    · simpa only [exactState,FrameSlots] using slots
    · exact ⟨rfl,rfl,rfl,rfl⟩
    · simp only [exactState]
    · simpa only [exactState] using SlotPrefix.refl raw.base.val exec.slots.val
    · exact machine.typed
    · exact machine.core
  · exact Or.inl ⟨rfl,dispatch_measure_forward _ _ _ _ forward point.code.current.entry_bound⟩
end Itasca.Interp.Machine

end

/-! ## UniformSimulation -/

section

/-!
A concrete-only rank for silent dispatches. It is independent of source function publication, stack depth, and the size of the current source store.

Main declarations: `silentDispatchPotential` and `UniformConcreteSim`.
-/

namespace Itasca.Interp
open Aeneas.Std

/-- A concrete-only rank for silent dispatches. It is independent of source
function publication, stack depth, and the size of the current source store. -/
def silentDispatchPotential (pending : Bool) (pc : Nat) : Nat :=
  (if pending then U32.max + 1 else 0) + (U32.max - pc)

theorem silent_dispatch_potential_forward {beforePC afterPC : Nat}
    (forward : beforePC < afterPC) (bound : afterPC ≤ U32.max) :
    silentDispatchPotential false afterPC < silentDispatchPotential false beforePC := by
  simp only [silentDispatchPotential, Bool.false_eq_true, ite_false]
  omega

/-- Stronger dispatch evidence retaining the concrete rank in the silent case.
The ordinary source relation alone cannot imply this extra PC fact. -/
def UniformConcreteSim (beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (before after : SourceMachine.AState) (events : List SpecExt.HostEvent) : Prop :=
  (SourceMachine.decode before = SourceMachine.decode after ∧ events = [] ∧
    silentDispatchPotential afterPending afterPC < silentDispatchPotential beforePending beforePC) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after)

theorem UniformConcreteSim.forward {beforePC afterPC : Nat} {before after : SourceMachine.AState}
    (same : SourceMachine.decode before = SourceMachine.decode after) (forward : beforePC < afterPC)
    (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false false before after [] :=
  Or.inl ⟨same, rfl, silent_dispatch_potential_forward forward bound⟩

theorem ConcreteSim.uniform_forward {codeLength beforePC afterPC : Nat} {before after : SourceMachine.AState}
    (simulation : ConcreteSim codeLength beforePC afterPC false false before after)
    (forward : beforePC < afterPC) (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false false before after [] := by
  rcases simulation with ⟨same,_⟩ | reductions
  · exact .forward same forward bound
  · exact Or.inr reductions

theorem UniformConcreteSim.of_steps {beforePC afterPC beforePending afterPending before after events n}
    (positive : 0 < n) (steps : Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after)) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after events :=
  Or.inr ⟨n,positive,steps⟩

end Itasca.Interp

end

/-! ## UniformSource -/

section

/-!
An unchanged source state cancels the old source potential. Hence an ordinary-phase silent dispatch must move forward, independent of code size.

Main declarations: `ConcreteSim.uniform_same` and `UniformConcreteSim.single`.
-/

namespace Itasca.Interp
open Aeneas.Std SpecExt Itasca.Spec

/-- An unchanged source state cancels the old source potential. Hence an
ordinary-phase silent dispatch must move forward, independent of code size. -/
theorem ConcreteSim.uniform_same {codeLength beforePC afterPC : Nat}
    {pending : Bool} {source : SourceMachine.AState}
    (simulation : ConcreteSim codeLength beforePC afterPC false pending source source)
    (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false pending source source [] := by
  rcases simulation with ⟨same,decrease⟩ | reductions
  · cases pending with
    | false =>
      have forward : beforePC < afterPC := by
        simp only [dispatchMeasure, Bool.false_eq_true, ite_false] at decrease
        omega
      exact UniformConcreteSim.forward rfl forward bound
    | true =>
      simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true] at decrease
      omega
  · exact Or.inr reductions

theorem UniformConcreteSim.single {beforePC afterPC beforePending afterPending before after events}
    (step : StepH (SourceMachine.decode before) events (SourceMachine.decode after)) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after events :=
  .of_steps (by omega : 0 < 1)
    (by simpa only [List.append_nil] using StepsHN.cons step (StepsHN.refl (step_h_wf step).2))
end Itasca.Interp

end

/-! ## BranchSource -/

section

/-!
A fused conditional branch always performs the source test and, when selected, the positive branch transfer.

Main declarations: `branch_if_source_positive`.
-/

namespace Itasca.Interp
open Aeneas.Std SpecExt Itasca.Spec

/-- A fused conditional branch always performs the source test and, when
selected, the positive branch transfer. -/
theorem branch_if_source_positive (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (label : SourceMachine.Label) (front discarded results : List val) (value : Nat)
    (bound : value < 2 ^ 32) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (arity : label.arity = results.length)
    (types : results.map SourceMachine.valueType = label.branchTypes)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩) :
    ∃ count, 0 < count ∧ StepsHN count
      (SourceMachine.decode ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩)
      [] (SourceMachine.decode ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩) := by
  have step := branch_if_source_step s ambient f rest after depth (front ++ discarded ++ results) value bound
  have typedNext := SourceMachine.instruction_preservation s ambient
    { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  have first := SourceMachine.typed_br_if_positive s ambient
    { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } rest
    after depth _ typed step
  have counted := StepsHN.cons first (StepsHN.refl (step_h_wf first).2)
  by_cases zero : value = 0
  · refine ⟨1,by omega,?_⟩
    simpa only [branchIfFrame,if_pos zero,List.nil_append] using counted
  · simp only [if_neg zero] at typedNext counted
    have branch := branch_source_step s ambient f rest after depth label front discarded results lookup height arity types
    have branchCounted := SourceMachine.typed_branch_simulation s ambient { f with vals := front ++ discarded ++ results } rest
      after depth _ typedNext branch
    refine ⟨1+(depth+1),by omega,?_⟩
    simpa only [branchIfFrame,if_neg zero,List.nil_append] using counted.trans branchCounted
end Itasca.Interp

end

end
