import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Control.LabelCompletion

/-!
Sections, each formerly its own module: ForwardJump, ControlInversion, LabelCompletion, BranchInversion, BranchPoint.
-/

/-! ## ForwardJump -/

section

/-!
A retained forward jump is a source stutter with a strictly decreasing administrative measure. It preserves all slot words and mutable store data.

Main declarations: `step_forward_jump_flat`. A direct consumer is `Interp.Machine.Memory`.
-/

namespace Itasca.Runtime.Interp.Machine
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
end Itasca.Runtime.Interp.Machine

end

/-! ## ControlInversion -/

section

/-!
Inversion of block, loop and if code relations.

Main declarations: `code_rel_block_inv` and `code_rel_if_inv`. A direct consumer is `Interp.Machine.Normalization`.
-/

namespace Itasca.Runtime.Interp.Machine
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
      cond.val = Compiler.slots C.LOCALS + Compiler.slots (front ++ params) ∧
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


end Itasca.Runtime.Interp.Machine

end

/-! ## LabelCompletion -/

section

/-!
Normal completion removes a source label at its retained fallthrough PC. The concrete words and PC are unchanged; the generated source semantics takes one positive reduction and installs the retained enclosing continuation.

Main declarations: `label_completion_point`. A direct consumer is `Interp.Machine.Normalization`.
-/

namespace Itasca.Runtime.Interp.Machine
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
  have valueTypes : f.vals.map Compiler.valueType = target.front ++ target.resultTypes := by
    rw [matching.front, matching.resultTypes]
    have resultTypes : (f.vals.drop label.height).map Compiler.valueType = label.resultTypes := by
      simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using results
    rw [← resultTypes, ← List.map_append, List.take_append_drop]
  refine ⟨next', output', slots, ⟨point.bindings,point.locals,?_, ?_⟩, ?_, ?_⟩
  · simpa only [List.drop_succ_cons, List.drop_zero] using point.labels.drop 1
  · exact ⟨by simpa only [Nat.zero_add, matching.after, pc, valueTypes] using relation,
      point.code.targets.drop 1, point.code.normal.drop 1, by simpa only [Nat.zero_add] using aligned, by simpa only [Nat.zero_add] using root⟩
  · exact SourceMachine.active_frame_preservation typed (SourceMachine.label_exit_frame_preservation frameTyped) rfl
  · exact SourceMachine.typed_label_end_simulation s ambient f rest label labels _ typed step

end Itasca.Runtime.Interp.Machine

end

/-! ## BranchInversion -/

section

/-!
Inversion of direct and conditional branch code relations.

Main declarations: `code_rel_branch_inv` and `code_rel_branch_if_inv`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp.Machine
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
      Compiler.BranchLayout C.LOCALS before label dst src count ∧ cond.val = Compiler.slots C.LOCALS + Compiler.slots before ∧
      Compiler.Segment code pc (Compiler.branchIfInstructions dst src count label.target cond resume) resume.val ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels before after resume.val next output) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_br_if head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | branchIf lookup live layout condition fragment rest => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, lookup, live, layout, condition, fragment, rest⟩


end Itasca.Runtime.Interp.Machine

end

/-! ## BranchPoint -/

section

/-!
Target lookup exposes the retained source continuation, with concrete label fields obtained from the dynamic/static label correspondence.

Main declarations: `FramePoint.target` and `branch_target_point`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp.Machine
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
  have frontTypes : target.front = front.map Compiler.valueType := by
    simpa only [height, List.append_assoc, List.take_left] using matching.front
  have resultTypes : results.map Compiler.valueType = label.branchTypes := by
    simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types
  have outer := typed.outer_heights depth label lookup
  have labels := point.labels.branch depth (by simpa only [height] using outer)
  refine ⟨target, targetNext, targetOutput, found, matching, ⟨point.bindings,point.locals,labels, ?_⟩⟩
  simpa only [List.map_append, resultTypes, frontTypes] using continuation

theorem branch_target_point {s : _root_.store} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {compiled : runtime.bytecode.CompiledFunction}
    {C : context} {targets : List Compiler.LabelTarget}
    (front discarded results : List val)
    (bindings : SourceMachine.ModuleBindings s f.module C) (locals : C.LOCALS = f.locals.map Compiler.valueType)
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
  have frontTypes : target.front = front.map Compiler.valueType := by
    simpa only [height, List.append_assoc, List.take_left] using matching.front
  have resultTypes : results.map Compiler.valueType = label.branchTypes := by
    simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types
  have outer := typed.outer_heights depth label lookup
  have labels := matchingLabels.branch depth (by simpa only [height] using outer)
  refine ⟨target, targetNext, targetOutput, found, matching, ⟨bindings,locals,labels, ?_⟩⟩
  simpa only [List.map_append, resultTypes, frontTypes] using continuation

end Itasca.Runtime.Interp.Machine

end
