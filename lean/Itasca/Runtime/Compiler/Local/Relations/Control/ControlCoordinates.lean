import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Lowering.Emission.CopyContracts
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ClosingContracts
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra

/-!
Proofs for Runtime / Compiler / Local / Relations / Control.

This module collects ResolvedBranchPrefix, ControlCoordinates.
Each section documents its contracts and consumers.
-/

/-! ## ResolvedBranchPrefix -/

section

/-! ## BranchSuccessEmit -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
/-- Exact successful emission needs no separate vector-capacity or coordinate premise. -/
theorem compiler_emit_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    Emitted before after instruction := by
  exact (((runtime.compiler.FunctionCompiler.emit.inv ops before after instruction (.Ok ()) accepted).2 law).2 rfl).emitted

end Itasca.Compiler

end

/-! ## ResolvedBranchPrefix -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- Retargeting a newly emitted BR in its selected open group preserves the
previous resolved prefix and appends the final literal branch sequence. -/
theorem resolved_code_new_br (code : List Bytecode) (before after : List FixupTarget)
    (group : FixupTarget) (dst src count old : U32) (site : Usize)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (inside : FixupsInside (before ++ group :: after) code.length) :
    resolvedCode (code ++ branchInstructions dst src count old)
      (before ++ {group with sites := group.sites ++ [site]} :: after) =
      resolvedCode code (before ++ group :: after) ++ branchInstructions dst src count group.target := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simpa [branchInstructions, elided, BranchKind.instruction] using
      resolved_code_new_branch code [] before after group .jump old site (by simpa [elided] using position) inside
  · simpa [branchInstructions, elided, BranchKind.instruction, List.append_assoc] using
      resolved_code_new_branch code [transferInstruction dst src count] before after group .jump old site
        (by simpa [elided] using position) inside

end Itasca.Compiler

end

end

/-! ## ControlCoordinates -/

section

/-!
# Control Coordinates

Control cursor observations establish the source and emitted-code coordinates of structured callbacks.
-/

/-! ## ControlCursor -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

set_option maxRecDepth 4096
theorem compiler_enter_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  obtain ⟨prior, ctrl, signature, height, startPc, condition, source, middle,
    controls, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind blockType (.Ok ()) accepted).2.2 rfl
  have effect := compiler_observe ops law middle state
  rw [observed, WP.spec_ok] at effect
  exact (effect rfl).2.2.2.2.2.2.2.2.1

theorem compiler_branch_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    after.next_source = before.next_source := by
  have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional (.Ok ()) accepted).frame
  rw [frame]

theorem compiler_end_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  obtain ⟨middle, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind blockType (.Ok ()) accepted).observation
  exact compiler_observe_cursor ops law middle after state (.Ok ()) observed rfl

theorem compiler_else_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  obtain ⟨middle, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops before after state blockType (.Ok ()) accepted).observation
  have post := compiler_observe ops law middle state
  rw [observed, WP.spec_ok] at post
  exact (post rfl).2.2.2.2.2.2.2.2.1

end Itasca.Compiler

end

/-! ## ControlSources -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

set_option maxRecDepth 4096
theorem compiler_enter_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    SourceProgress before after := by
  obtain ⟨prior, ctrl, signature, height, startPc, condition, source, middle,
    controls, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind blockType (.Ok ()) accepted).2.2 rfl
  have publication := publish law
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  unfold SourceProgress
  rw [observedFrame]
  change middle.function.code.val.length + before.function.source_offsets.val.length =
    before.function.code.val.length + middle.function.source_offsets.val.length
  have lengths := congrArg List.length publication.sources
  simp only [List.length_map, List.length_append] at lengths
  rw [publication.code, List.length_append]
  omega

theorem compiler_branch_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold SourceProgress
  obtain ⟨_, count, code, sources⟩ := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional (.Ok ()) accepted).source_trace law
  have lengths := congrArg List.length sources
  simp only [List.length_map, List.length_append, List.length_replicate] at lengths
  omega
theorem compiler_end_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    SourceProgress before after := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind blockType (.Ok ()) accepted
  obtain ⟨frame, remaining, popped, frames, codeLength, sources⟩ := effect.sources_frames law
  have sourceLength := congrArg List.length sources
  simp only [List.length_map, List.length_append] at sourceLength
  unfold SourceProgress
  cases label : frame.kind <;> simp only [label, List.length_nil, List.length_singleton] at codeLength sourceLength <;> omega

theorem compiler_else_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    SourceProgress before after := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops before after state blockType (.Ok ()) accepted
  cases effect with
  | selected nonempty subtracted read progress =>
    obtain ⟨fixups, appended, frames, reachable, codeLength, sources, cursor⟩ := progress.success_fields law
    have sourceLength := congrArg List.length sources
    simp only [List.length_map, List.length_append] at sourceLength
    unfold SourceProgress
    cases live : before.reachable <;>
      simp only [live, Bool.false_eq_true, ite_false, ite_true, List.length_nil, List.length_singleton] at codeLength sourceLength <;> omega

end Itasca.Compiler

end

/-! ## BranchCertificates -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

def BranchHole (code : List Bytecode) (sites : List Usize)
    (pc : Nat) (dst src count : U32) : Prop :=
  if count = 0#u32 ∨ src = dst then
    ∃ site, site ∈ sites ∧ site.val = pc ∧ code[pc]? = some (.Jump 4294967295#u32)
  else
    code[pc]? = some (transferInstruction dst src count) ∧
    ∃ site, site ∈ sites ∧ site.val = pc + 1 ∧ code[pc + 1]? = some (.Jump 4294967295#u32)

end Itasca.Compiler

end

end
