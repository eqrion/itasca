import Itasca.Runtime.Compiler.Local.Lowering.Emission.CopyContracts
import Itasca.Runtime.Compiler.Local.Relations.Control
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra

/-!
Proofs for Runtime / Compiler / Local / Lowering / Control.

This module collects BranchContracts, BranchEffects, ExitContracts, TableBranchContracts.
Each section documents its contracts and consumers.
-/

/-! ## BranchContracts -/

section

open Itasca.Representation

/-! Canonical branch contracts retain the selected operand interval and the
ordered helper calls, including partial progress before ordinary errors.

Main declarations: `branch.inv`, `branch.total`, and `branch.available`. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

/-- Branching changes only the allocation budget, selected control frame, and
instruction/source buffers. This frame applies to every normal return. -/
def BranchFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget, frames := after.frames,
    function := {before.function with
      code := after.function.code,
      source_offsets := after.function.source_offsets}}

/-- Loop classification is independent of instruction constructors. -/
def branchLoop (kind : Itasca.code.LabelKind) : Bool :=
  match kind with | .Loop => true | _ => false

/-- The width transferred to a loop is its parameter width; other labels use
 their result width. -/
def branchWidth (frame : runtime.compiler.Frame) : U32 :=
  match frame.kind with | .Loop => frame.params | _ => frame.results

/-- A conditional transfer uses a separate guard; an elided conditional copy
uses the final jump itself as its guard. -/
def branchJump (conditional copying : Bool) (condition target : U32) : runtime.bytecode.Instr :=
  if conditional && !copying then .JumpIfNonZero condition target else .Jump target

/-- The final patch phase retains the actual PC and patch calls. -/
def BranchPatch {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (guard : Option Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  match guard with
  | none => status = .Ok () ∧ after = before
  | some site => ∃ answer middle,
    runtime.compiler.FunctionCompiler.pc ops before = .ok (answer, middle) ∧
    match answer with
    | .Err error => status = .Err error ∧ after = middle
    | .Ok target => runtime.compiler.control.FunctionCompiler.patch ops middle site target = .ok (status, after)

/-- The jump may fail after updating buffers; a successful jump proceeds to its
optional guard patch. -/
def BranchJumpCall {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (guard : Option Usize) (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ answer middle,
    runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (answer, middle) ∧
    match answer with
    | .Err error => status = .Err error ∧ after = middle
    | .Ok _ => BranchPatch ops middle after guard status

/-- Publication records the mutable frame lookup and the forward-fixup push.
Even a rejected push can return an updated budget and vector. -/
def BranchPublication {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (conditional copying : Bool) (condition : U32) (guard : Option Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ frame restore,
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
      before.frames index = .ok (frame, restore) ∧
    if branchLoop frame.kind then BranchJumpCall ops {before with frames := restore frame} after
        (branchJump conditional copying condition frame.start_pc) guard status
    else ∃ answer budget fixups,
        runtime.compiler.Budget.push ops before.budget frame.fixups
          (alloc.vec.Vec.len before.function.code) = .ok (answer, budget, fixups) ∧
        match answer with
        | .Err error => status = .Err error ∧
            after = {before with budget, frames := restore {frame with fixups}}
        | .Ok _ => BranchJumpCall ops
            {before with budget, frames := restore {frame with fixups, end_reachable := true}} after
            (branchJump conditional copying condition core.num.U32.MAX) guard status

/-- Copy elision does not consume resources. Nonelided copies retain their call
before the selected frame is published. -/
def BranchCopy {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (dst src count : U32) (conditional copying : Bool) (condition : U32)
    (guard : Option Usize) (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  if copying then ∃ answer middle,
    runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (answer, middle) ∧
    match answer with
    | .Err error => status = .Err error ∧ after = middle
    | .Ok _ => BranchPublication ops middle after index conditional copying condition guard status
  else BranchPublication ops before after index conditional copying condition guard status

/-- A conditional nonelided transfer first emits its skip guard. -/
def BranchTransfer {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (dst src count : U32) (conditional : Bool) (condition : U32)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  let copying := count != 0#u32 && src != dst
  if conditional && copying then ∃ answer middle,
    runtime.compiler.FunctionCompiler.emit ops before (.JumpIfZero condition core.num.U32.MAX) =
      .ok (answer, middle) ∧
    match answer with
    | .Err error => status = .Err error ∧ after = middle
    | .Ok _ => BranchCopy ops middle after index dst src count conditional copying condition
        (some (alloc.vec.Vec.len before.function.code)) status
  else BranchCopy ops before after index dst src count conditional copying condition none status

/-- Operand lookup is needed only for conditional branches. -/
def BranchCondition {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (dst src count : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  if conditional then ∃ answer,
    runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok answer ∧
    match answer with
    | .Err error => status = .Err error ∧ after = before
    | .Ok condition => BranchTransfer ops before after index dst src count conditional condition status
  else BranchTransfer ops before after index dst src count conditional 0#u32 status

/-- Checked addition/subtraction can reject before any mutation or allocation. -/
def BranchSource {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (frame : runtime.compiler.Frame) (skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ sum, lift (U32.checked_add skip (branchWidth frame)) = .ok sum ∧
    match sum with
    | none => status = .Err .OutOfMemory ∧ after = before
    | some width => ∃ source, lift (U32.checked_sub before.height width) = .ok source ∧
      match source with
      | none => status = .Err .OutOfMemory ∧ after = before
      | some src => BranchCondition ops before after index frame.height src (branchWidth frame) conditional status

/-- A branch return records the exact index calculation and ordered effects.
No allocator correctness premise is needed for this operational evidence. -/
def BranchEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ last converted index frame,
    (alloc.vec.Vec.len before.frames - 1#usize : Result Usize) = .ok last ∧
    lift (UScalar.cast .Usize depth) = .ok converted ∧
    (last - converted : Result Usize) = .ok index ∧
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
      before.frames index = .ok frame ∧
    BranchSource ops before after index frame skip conditional status

theorem BranchFrame.refl {A : Type} (before : runtime.compiler.FunctionCompiler A) : BranchFrame before before := rfl

theorem BranchFrame.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : BranchFrame before middle) (second : BranchFrame middle after) : BranchFrame before after := by
  unfold BranchFrame at *
  rw [second, first]

theorem EmitFrame.branch {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EmitFrame before after) : BranchFrame before after := by
  unfold EmitFrame at effect
  unfold BranchFrame
  rw [effect]

theorem BranchPatch.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {guard status}
    (effect : BranchPatch ops before after guard status) : BranchFrame before after := by
  cases guard with
  | none => exact effect.2 ▸ BranchFrame.refl before
  | some site =>
    obtain ⟨answer, middle, called, rest⟩ := effect
    have pc := compiler_pc ops before
    rw [called, WP.spec_ok] at pc
    obtain ⟨budget, same⟩ := pc.2.2
    change middle = {before with budget} at same
    have firstFrame : BranchFrame before middle := by rw [same]; rfl
    apply firstFrame.trans
    cases answer with
    | Err error => exact rest.2 ▸ BranchFrame.refl middle
    | Ok target =>
      rcases compiler_patch_cases ops middle after site target status rest with same | ⟨instruction, code, same, _⟩
      · rw [same]; rfl
      · rw [same]; rfl

theorem BranchJumpCall.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard status}
    (effect : BranchJumpCall ops before after instruction guard status) : BranchFrame before after := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  have firstFrame := (runtime.compiler.FunctionCompiler.emit.inv ops before middle instruction answer called).1.branch
  apply firstFrame.trans
  cases answer with
  | Err error => exact rest.2 ▸ BranchFrame.refl middle
  | Ok value => exact rest.frame

theorem BranchPublication.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard status}
    (effect : BranchPublication ops before after index conditional copying condition guard status) : BranchFrame before after := by
  obtain ⟨frame, restore, _, rest⟩ := effect
  split at rest
  · exact (show BranchFrame before {before with frames := restore frame} from rfl).trans rest.frame
  · obtain ⟨answer, budget, fixups, _, rest⟩ := rest
    cases answer with
    | Err error => rw [rest.2]; rfl
    | Ok value =>
      exact (show BranchFrame before {before with budget, frames := restore {frame with fixups, end_reachable := true}} from rfl).trans rest.frame

theorem BranchCopy.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard status}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard status) : BranchFrame before after := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    have firstFrame := (runtime.compiler.FunctionCompiler.copy.inv ops before middle dst src count answer called).frame.branch
    apply firstFrame.trans
    cases answer with
    | Err error => exact rest.2 ▸ BranchFrame.refl middle
    | Ok value => exact rest.frame
  · exact effect.frame

theorem BranchTransfer.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition status}
    (effect : BranchTransfer ops before after index dst src count conditional condition status) : BranchFrame before after := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    have firstFrame := (runtime.compiler.FunctionCompiler.emit.inv ops before middle _ answer called).1.branch
    apply firstFrame.trans
    cases answer with
    | Err error => exact rest.2 ▸ BranchFrame.refl middle
    | Ok value => exact rest.frame
  · exact effect.frame

theorem BranchCondition.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional status}
    (effect : BranchCondition ops before after index dst src count conditional status) : BranchFrame before after := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => exact rest.2 ▸ BranchFrame.refl before
    | Ok condition => exact rest.frame
  · exact effect.frame

theorem BranchSource.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional status}
    (effect : BranchSource ops before after index frame skip conditional status) : BranchFrame before after := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => exact rest.2 ▸ BranchFrame.refl before
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => exact rest.2 ▸ BranchFrame.refl before
    | some src => exact rest.frame

theorem BranchEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional status}
    (effect : BranchEffect ops before after depth skip conditional status) : BranchFrame before after := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.frame

/-- Inversion records every primitive branch phase without allocator assumptions. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.branch.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional =
      .ok (status, after)) : BranchEffect ops before after depth skip conditional status := by
  unfold runtime.compiler.control.FunctionCompiler.branch at called
  obtain ⟨last, lastRun, rest⟩ := bind_ok_inv _ _ _ called
  clear called
  obtain ⟨converted, convertedRun, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨index, indexRun, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨frame, frameRun, rest⟩ := bind_ok_inv _ _ _ rest
  refine ⟨last, converted, index, frame, lastRun, convertedRun, indexRun, frameRun, ?_⟩
  obtain ⟨loop, loopRun, rest⟩ := bind_ok_inv _ _ _ rest
  have loopEq : loop = branchLoop frame.kind := by
    cases kind : frame.kind <;>
      simp only [kind, branchLoop, Result.ok.injEq] at loopRun ⊢ <;> exact loopRun.symm
  subst loop
  obtain ⟨count, countRun, rest⟩ := bind_ok_inv _ _ _ rest
  have countEq : count = branchWidth frame := by
    cases kind : frame.kind <;>
      simp only [kind, branchLoop, branchWidth, Bool.true_eq, Bool.false_eq_true,
        ite_true, ite_false, Result.ok.injEq] at countRun ⊢ <;> exact countRun.symm
  subst count
  obtain ⟨sum, sumRun, rest⟩ := bind_ok_inv _ _ _ rest
  refine ⟨sum, sumRun, ?_⟩
  cases sum with
  | none =>
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact ⟨rest.1.symm, rest.2.symm⟩
  | some width =>
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨source, sourceRun, rest⟩ := bind_ok_inv _ _ _ rest
    refine ⟨source, sourceRun, ?_⟩
    cases source with
    | none =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      exact ⟨rest.1.symm, rest.2.symm⟩
    | some src =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      cases conditional <;>
        simp only [BranchCondition, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at rest ⊢
      all_goals first
        | change BranchTransfer ops before after index frame.height src (branchWidth frame) false 0#u32 status
        | (obtain ⟨answer, operandRun, rest⟩ := bind_ok_inv _ _ _ rest
           refine ⟨answer, operandRun, ?_⟩
           cases answer <;>
             simp only [core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
           all_goals first | exact ⟨rest.1.symm, rest.2.symm⟩ | skip)
      all_goals
        obtain ⟨copying, copyRun, rest⟩ := bind_ok_inv _ _ _ rest
        have copyEq : copying = ((branchWidth frame != 0#u32) && (src != frame.height)) := by
          cases nonzero : (branchWidth frame != 0#u32) <;>
            simp only [nonzero, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false,
              Bool.false_and, Bool.true_and, Result.ok.injEq] at copyRun ⊢ <;> exact copyRun.symm
        subst copying
        unfold BranchTransfer
        cases copyFlag : ((branchWidth frame != 0#u32) && (src != frame.height)) <;>
          simp only [copyFlag, Bool.true_eq, Bool.false_eq_true, Bool.false_and,
            Bool.true_and, ite_true, ite_false, bind_ok] at rest ⊢
      all_goals first
        | change BranchCopy ops _ after index frame.height src (branchWidth frame) _ _ _ _ status
        | (obtain ⟨⟨answer, middle⟩, emitRun, rest⟩ := bind_ok_inv _ _ _ rest
           refine ⟨answer, middle, emitRun, ?_⟩
           cases answer <;>
             simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
           all_goals first | exact ⟨rest.1.symm, rest.2.symm⟩ | skip)
      all_goals
        unfold BranchCopy
        simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
      all_goals first
        | change BranchPublication ops _ after index _ _ _ _ status
        | (obtain ⟨⟨answer, middle⟩, copyRun, rest⟩ := bind_ok_inv _ _ _ rest
           refine ⟨answer, middle, copyRun, ?_⟩
           cases answer <;>
             simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
           all_goals first | exact ⟨rest.1.symm, rest.2.symm⟩ | skip)
      all_goals
        obtain ⟨⟨selected, restore⟩, frameRead, rest⟩ := bind_ok_inv _ _ _ rest
        refine ⟨selected, restore, frameRead, ?_⟩
        obtain ⟨⟨kind, loop⟩, kindRun, rest⟩ := bind_ok_inv _ _ _ rest
        have kindEq : (kind, loop) = (selected.kind, branchLoop selected.kind) := by
          cases selectedKind : selected.kind <;>
            simp only [selectedKind, branchLoop, Result.ok.injEq] at kindRun ⊢ <;> exact kindRun.symm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj kindEq
        cases loopFlag : branchLoop selected.kind <;>
          simp only [loopFlag, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false,
            bind_ok, uncurry_apply_pair] at rest ⊢
      all_goals first
        | change BranchJumpCall ops _ after _ _ status
        | (obtain ⟨⟨answer, budget, fixups⟩, pushRun, rest⟩ := bind_ok_inv _ _ _ rest
           refine ⟨answer, budget, fixups, pushRun, ?_⟩
           cases answer <;>
             simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
           all_goals first | exact ⟨rest.1.symm, rest.2.symm⟩ | skip)
      all_goals
        simp only [branchJump, Bool.not_true, Bool.not_false, Bool.false_and,
          Bool.true_and, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
        obtain ⟨⟨answer, middle⟩, emitRun, rest⟩ := bind_ok_inv _ _ _ rest
        refine ⟨answer, middle, emitRun, ?_⟩
        cases answer <;>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        all_goals first | exact ⟨rest.1.symm, rest.2.symm⟩ | skip
      all_goals
        unfold BranchPatch
        first
        | (have equal := Result.ok_injective rest
           exact ⟨(congrArg Prod.fst equal).symm, (congrArg Prod.snd equal).symm⟩)
        | (obtain ⟨⟨answer, middle⟩, pcRun, rest⟩ := bind_ok_inv _ _ _ rest
           refine ⟨answer, middle, pcRun, ?_⟩
           cases answer with
           | Err error =>
             simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
             exact ⟨rest.1.symm, rest.2.symm⟩
           | Ok target =>
             simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
             obtain ⟨⟨answer, final⟩, patchRun, rest⟩ := bind_ok_inv _ _ _ rest
             cases answer with
             | Err error =>
               simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                 core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                 core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
               obtain ⟨rfl, rfl⟩ := rest
               exact patchRun
             | Ok value =>
               cases value
               simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                 bind_ok, Result.ok.injEq, Prod.mk.injEq] at rest
               obtain ⟨rfl, rfl⟩ := rest
               exact patchRun)
/-- A selected control frame supplies the safety condition for the unchecked
frame indexing at the start of branch lowering. -/
structure BranchSelection {A : Type} (before : runtime.compiler.FunctionCompiler A) (depth : U32) where
  index : Usize
  frame : runtime.compiler.Frame
  lookup : before.frames.val[index.val]? = some frame
  position : index.val + depth.val + 1 = before.frames.val.length

/-- Exact number of emitted instructions, including a conditional transfer's
separate guard. Even an elided transfer emits its final jump. -/
def branchInstructionCount (conditional : Bool) (frame : runtime.compiler.Frame) (source : U32) : Nat :=
  if branchWidth frame = 0#u32 ∨ source = frame.height then 1
  else if conditional then 3 else 2

/-- Normality only requires representable appends, not successful allocation or
instruction-budget availability. -/
structure BranchTotalBounds {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (count : Nat) : Prop where
  code : before.function.code.length + count ≤ Usize.max
  sources : before.function.source_offsets.length + count ≤ Usize.max
  coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max
  fixups : frame.kind ≠ .Loop → frame.fixups.length < Usize.max

/-- Independent room for an instruction sequence. Its final PC is also bounded
so a conditional guard can target the point after the sequence. -/
structure BranchCapacity {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (bound count : Nat) : Prop where
  pc : before.function.code.length + count ≤ U32.max
  code : before.function.code.length + count ≤ Usize.max
  sources : before.function.source_offsets.length + count ≤ Usize.max
  codeReserve : before.function.code.length + count ≤ bound
  sourceReserve : before.function.source_offsets.length + count ≤ bound
  coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max
  instructions : before.budget.instructions.val + count ≤ before.budget.limits.max_instructions.val

/-- Forward targets additionally require one fixup-vector append. -/
structure BranchDemand {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (bound count : Nat) : Prop extends BranchCapacity before bound count where
  fixups : frame.kind ≠ .Loop → frame.fixups.length < Usize.max
  fixupsReserve : frame.kind ≠ .Loop → frame.fixups.length + 1 ≤ bound

/-- Successful branch lowering charges only instructions. -/
def BranchBudget {A : Type} (before after : runtime.compiler.FunctionCompiler A) (count : Nat) : Prop :=
  ∃ instructions,
    after.budget = {before.budget with instructions} ∧
    instructions.val = before.budget.instructions.val + count

/-- One remaining instruction supplies the primitive emission requirements. -/
theorem BranchCapacity.one {A : Type} {before : runtime.compiler.FunctionCompiler A}
    {bound count : Nat} (room : BranchCapacity before bound count) (positive : 0 < count) :
    CopyDemand before bound := by
  exact ⟨by have h := room.pc; omega,
    by have h := room.code; omega, by have h := room.sources; omega,
    by have h := room.codeReserve; omega, by have h := room.sourceReserve; omega,
    room.coordinate, by have h := room.instructions; omega⟩

/-- Exact successful emission consumes one unit of each independent capacity. -/
theorem BranchCapacity.after_emission {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {bound count : Nat}
    {instruction : runtime.bytecode.Instr}
    (room : BranchCapacity before bound (count + 1)) (emitted : EmittedExact before after instruction) :
    BranchCapacity after bound count := by
  obtain ⟨used, code, sources, rfl, charged, appended, recorded⟩ := emitted
  have codeLength : code.val.length = before.function.code.val.length + 1 := by
    rw [appended]
    simp only [List.length_append, List.length_cons, List.length_nil]
  have sourceLength := congrArg List.length recorded
  simp only [List.length_map, List.length_append, List.length_cons, List.length_nil] at sourceLength
  rcases room with ⟨pc, codeRoom, sourcesRoom, codeReserve, sourceReserve, coordinate, instructions⟩
  simp only [alloc.vec.Vec.length] at pc codeRoom sourcesRoom codeReserve sourceReserve
  exact ⟨by change code.val.length + count ≤ U32.max; omega,
    by change code.val.length + count ≤ _; omega,
    by change sources.val.length + count ≤ _; omega,
    by change code.val.length + count ≤ _; omega,
    by change sources.val.length + count ≤ _; omega,
    coordinate, by change used.val + count ≤ before.budget.limits.max_instructions.val; omega⟩

theorem BranchCapacity.with_frames {A : Type} {before : runtime.compiler.FunctionCompiler A}
    {bound count : Nat} (room : BranchCapacity before bound count)
    (frames : alloc.vec.Vec runtime.compiler.Frame) :
    BranchCapacity {before with frames} bound count := by
  exact ⟨room.pc, room.code, room.sources, room.codeReserve, room.sourceReserve, room.coordinate, room.instructions⟩

theorem BranchBudget.refl {A : Type} (before : runtime.compiler.FunctionCompiler A) :
    BranchBudget before before 0 := by
  exact ⟨before.budget.instructions, rfl, (Nat.add_zero _).symm⟩

theorem BranchBudget.emitted {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : EmittedExact before after instruction) :
    BranchBudget before after 1 := by
  obtain ⟨used, code, sources, rfl, charged, _, _⟩ := emitted
  exact ⟨used, rfl, charged⟩

theorem BranchBudget.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    {left right : Nat} (first : BranchBudget before middle left) (second : BranchBudget middle after right) :
    BranchBudget before after (left + right) := by
  obtain ⟨used, budget, charged⟩ := first
  obtain ⟨final, finalBudget, finalCharged⟩ := second
  refine ⟨final, ?_, ?_⟩
  · rw [finalBudget, budget]
  · have middleInstructions : middle.budget.instructions = used := by rw [budget]
    rw [middleInstructions] at finalCharged
    omega

/-- Successful emission also transports the remaining sequence capacity. -/
private theorem branch_emit_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (count : Nat)
    (room : BranchCapacity before bound (count + 1)) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.FunctionCompiler.emit ops before instruction ⦃ (status, after) =>
      status = .Ok () ∧ EmittedExact before after instruction ∧
      BranchCapacity after bound count ∧ BranchBudget before after 1 ⦄ := by
  have one := room.one (by omega)
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.emit.available ops bound available before instruction
    one.pc one.codeCapacity one.sourceCapacity one.codeReserve one.sourceReserve one.coordinate one.instruction)
  intro output effect
  exact ⟨effect.1, effect.2, room.after_emission effect.2, BranchBudget.emitted effect.2⟩

/-- A nonelided transfer consumes exactly one reserved instruction. -/
private theorem branch_copy_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (count : Nat)
    (room : BranchCapacity before bound (count + 1)) (dst src width : U32)
    (nonelided : ¬ (width = 0#u32 ∨ src = dst)) :
    runtime.compiler.FunctionCompiler.copy ops before dst src width ⦃ (status, after) =>
      status = .Ok () ∧ EmittedExact before after (transferInstruction dst src width) ∧
      BranchCapacity after bound count ∧ BranchBudget before after 1 ⦄ := by
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.copy.available ops bound available before dst src width
    (fun _ _ => room.one (by omega)))
  intro output effect
  have emitted := effect.2
  rw [if_neg nonelided] at emitted
  exact ⟨effect.1, emitted, room.after_emission emitted, BranchBudget.emitted emitted⟩

/-- Independent allocation and exact branch demand guarantee successful
lowering and the exact instruction charge, using allocation availability alone. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.branch.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (depth skip : U32) (conditional : Bool)
    (selected : BranchSelection before depth) (source : U32)
    (sourcePosition : source.val + (branchWidth selected.frame).val + skip.val = before.height.val)
    (conditionReady : conditional = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition))
    (demand : BranchDemand before selected.frame bound (branchInstructionCount conditional selected.frame source)) :
    runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional ⦃ (status, after) =>
      status = .Ok () ∧ BranchBudget before after (branchInstructionCount conditional selected.frame source) ⦄ := by
  rcases selected with ⟨index, frame, lookup, position⟩
  dsimp only at sourcePosition demand ⊢
  have heightBound : before.height.val ≤ U32.max := by scalar_tac
  unfold runtime.compiler.control.FunctionCompiler.branch
  step as ⟨last, lastValue⟩
  step as ⟨converted, convertedValue⟩
  step as ⟨actualIndex, indexValue⟩
  have sameIndex : actualIndex = index := by
    apply UScalar.eq_of_val_eq
    simp only [alloc.vec.Vec.len] at lastValue
    scalar_tac
  subst actualIndex
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨found, foundValue⟩
  have sameFrame : found = frame := foundValue.trans (List.getElem?_eq_some_iff.mp lookup).2
  rw [sameFrame]
  apply WP.spec_bind (Pₘ := fun value => value = branchLoop frame.kind)
  · cases kind : frame.kind <;> simp only [kind, branchLoop, WP.spec_ok]
  intro loop loopEq
  subst loop
  apply WP.spec_bind (Pₘ := fun value => value = branchWidth frame)
  · cases kind : frame.kind <;> simp only [kind, branchLoop, branchWidth, Bool.true_eq,
      Bool.false_eq_true, ite_true, ite_false, WP.spec_ok]
  intro width widthEq
  subst width
  step as ⟨sum, sumValue⟩
  cases sum with
  | none =>
    dsimp only at sumValue
    omega
  | some sum =>
    dsimp only at sumValue
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨src, sourceValue⟩
    cases src with
    | none =>
      dsimp only at sourceValue
      omega
    | some src =>
      dsimp only at sourceValue
      have sameSource : src = source := by
        apply UScalar.eq_of_val_eq
        omega
      subst src
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]

      cases conditional <;>
        simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
      all_goals try
        obtain ⟨condition, conditionRun⟩ := conditionReady rfl
        rw [conditionRun]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      all_goals by_cases elided : branchWidth frame = 0#u32 ∨ source = frame.height
      all_goals first
        | (have yes : branchWidth frame = 0#u32 ∨ source = frame.height := elided
           have flag : (if branchWidth frame != 0#u32 then Result.ok (source != frame.height)
               else Result.ok false) = Result.ok false := by
             rcases yes with zero | same
             · rw [zero]
               simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
             · rw [same]
               simp only [bne_self_eq_false, ite_self]
           rw [flag]
           simp only [bind_ok, Bool.false_eq_true, ite_false, Bool.true_eq, ite_true]
           simp only [branchInstructionCount, if_pos yes] at demand ⊢)
        | (have no : ¬ (branchWidth frame = 0#u32 ∨ source = frame.height) := elided
           have countNe : branchWidth frame ≠ 0#u32 := fun equal => no (Or.inl equal)
           have sourceNe : source ≠ frame.height := fun equal => no (Or.inr equal)
           have flag : (if branchWidth frame != 0#u32 then Result.ok (source != frame.height)
               else Result.ok false) = Result.ok true := by
             have a : (branchWidth frame != 0#u32) = true := by simpa only [bne_iff_ne] using countNe
             have b : (source != frame.height) = true := by simpa only [bne_iff_ne] using sourceNe
             rw [a, b]
             rfl
           rw [flag]
           simp only [bind_ok, Bool.false_eq_true, ite_false, Bool.true_eq, ite_true]
           simp only [branchInstructionCount, if_neg no, Bool.true_eq, Bool.false_eq_true,
             ite_true, ite_false] at demand ⊢)
      all_goals try
        have guardCapacity : BranchCapacity before bound 3 := demand.toBranchCapacity
        step with branch_emit_available ops bound available before 2 guardCapacity
          (.JumpIfZero condition core.num.U32.MAX)
          as ⟨answer, afterGuard, accepted, guardEmission, guardRoom, guardBudget⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨guardUsed, guardCode, guardSources, rfl, guardCharge, guardAppended, guardRecorded⟩ := guardEmission
        have guardAt : guardCode.val[before.function.code.val.length]? =
            some (.JumpIfZero condition core.num.U32.MAX) := by
          simp only [guardAppended, List.getElem?_concat_length]
      all_goals try
        have copyCapacity : BranchCapacity before bound 2 := demand.toBranchCapacity
        step with branch_copy_available ops bound available before 1 copyCapacity
          frame.height source (branchWidth frame) elided
          as ⟨answer, afterCopy, accepted, copyEmission, copyRoom, copyBudget⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        try have copiedGuard := copyEmission.emitted.old_instruction guardAt
        obtain ⟨copyUsed, copyCode, copySources, rfl, copyCharge, copyAppended, copyRecorded⟩ := copyEmission
      all_goals try
        step with branch_copy_available ops bound available _ 1 guardRoom
          frame.height source (branchWidth frame) elided
          as ⟨answer, afterCopy, accepted, copyEmission, copyRoom, copyBudget⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        try have copiedGuard := copyEmission.emitted.old_instruction guardAt
        obtain ⟨copyUsed, copyCode, copySources, rfl, copyCharge, copyAppended, copyRecorded⟩ := copyEmission
      all_goals
        step as ⟨current, restore, currentValue, restoreValue⟩
        have currentEq : current = frame := currentValue.trans (List.getElem?_eq_some_iff.mp lookup).2
        rw [currentEq]
        apply WP.spec_bind (Pₘ := fun pair => pair = (frame.kind, branchLoop frame.kind))
        · cases kind : frame.kind <;> simp only [kind, branchLoop, WP.spec_ok]
        intro pair pairEq
        subst pair
        simp only [uncurry_apply_pair]
        cases loopFlag : branchLoop frame.kind <;>
          simp only [loopFlag, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false, bind_ok]
      all_goals try
        have forward : frame.kind ≠ .Loop := by
          intro same
          simp only [same, branchLoop] at loopFlag
          contradiction
        step with budget_push_available ops bound available _ frame.fixups _
          (demand.fixups forward) (demand.fixupsReserve forward)
          as ⟨answer, budget, fixups, accepted, sameBudget, appendedFixups⟩
        subst answer budget
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
      all_goals
        first
        | let readyFrames := restore {frame with end_reachable := true, fixups}
        | let readyFrames := restore frame
        first
        | (let ready : runtime.compiler.FunctionCompiler A := {before with
             budget := {before.budget with instructions := copyUsed}
             function := {before.function with code := copyCode, source_offsets := copySources}
             frames := readyFrames}
           have readyRoom : BranchCapacity ready bound 1 := copyRoom.with_frames readyFrames)
        | (let ready : runtime.compiler.FunctionCompiler A := {before with frames := readyFrames}
           have readyRoom : BranchCapacity ready bound 1 := demand.toBranchCapacity.with_frames readyFrames)
        first
        | (have isLoop : branchLoop frame.kind = true := loopFlag
           let target := frame.start_pc)
        | let target := core.num.U32.MAX
        first
        | (have one : BranchDemand before frame bound 1 := demand
           let instruction := runtime.bytecode.Instr.JumpIfNonZero condition target)
        | let instruction := runtime.bytecode.Instr.Jump target
        step with branch_emit_available ops bound available ready 0 readyRoom instruction
          as ⟨answer, afterJump, accepted, jumpEmission, jumpRoom, jumpBudget⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        try simp only [WP.spec_ok]
        try have finalGuard := jumpEmission.emitted.old_instruction copiedGuard
        obtain ⟨finalUsed, finalCode, finalSources, rfl, finalCharge, finalAppended, finalRecorded⟩ := jumpEmission
        dsimp only at finalCharge
        try dsimp only at copyCharge
        try dsimp only at guardCharge
      all_goals first
        | (change core.result.Result.Ok () = core.result.Result.Ok () ∧ BranchBudget before _ _
           refine ⟨rfl, finalUsed, rfl, ?_⟩
           omega)
        | skip
      all_goals
        let emitted : runtime.compiler.FunctionCompiler A := {ready with
          budget := {ready.budget with instructions := finalUsed}
          function := {ready.function with code := finalCode, source_offsets := finalSources}}
        step with compiler_pc_available ops emitted (by simpa only [Nat.add_zero] using jumpRoom.pc)
          as ⟨answer, afterPc, sameCompiler, target, accepted, targetValue⟩
        subst afterPc answer
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have guardLookup : finalCode.val[(alloc.vec.Vec.len before.function.code).val]? =
            some (BranchKind.instruction (.zero condition) core.num.U32.MAX) := by
          simpa only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, BranchKind.instruction] using finalGuard
        step with runtime.compiler.control.FunctionCompiler.patch.available ops emitted
          (alloc.vec.Vec.len before.function.code) (.zero condition) core.num.U32.MAX target guardLookup
          as ⟨answer, afterPatch, accepted, patched⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
        obtain ⟨patchedCode, rfl, patchedValues⟩ := patched
        refine ⟨rfl, finalUsed, rfl, ?_⟩
        omega

/-- Successful emission consumes one append slot in a normality bound. -/
private theorem BranchTotalBounds.after_emission {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {frame : runtime.compiler.Frame} {count : Nat}
    {instruction : runtime.bytecode.Instr} (room : BranchTotalBounds before frame (count + 1))
    (emitted : Emitted before after instruction) : BranchTotalBounds after frame count := by
  obtain ⟨budget, code, sources, rfl, appended, recorded⟩ := emitted
  have codeLength : code.val.length = before.function.code.val.length + 1 := by
    rw [appended]
    simp only [List.length_append, List.length_cons, List.length_nil]
  have sourceLength := congrArg List.length recorded
  simp only [List.length_map, List.length_append, List.length_cons, List.length_nil] at sourceLength
  rcases room with ⟨codeRoom, sourceRoom, coordinate, fixups⟩
  simp only [alloc.vec.Vec.length] at codeRoom sourceRoom
  exact ⟨by change code.val.length + count ≤ Usize.max; omega,
    by change sources.val.length + count ≤ Usize.max; omega, coordinate, fixups⟩

private theorem BranchTotalBounds.with_frames {A : Type} {before : runtime.compiler.FunctionCompiler A}
    {frame : runtime.compiler.Frame} {count : Nat} (room : BranchTotalBounds before frame count)
    (frames : alloc.vec.Vec runtime.compiler.Frame) : BranchTotalBounds {before with frames} frame count := by
  exact ⟨room.code, room.sources, room.coordinate, room.fixups⟩

private theorem branch_emit_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (count : Nat) (room : BranchTotalBounds before frame (count + 1))
    (instruction : runtime.bytecode.Instr) :
    runtime.compiler.FunctionCompiler.emit ops before instruction ⦃ (status, after) =>
      status = .Ok () → Emitted before after instruction ∧ BranchTotalBounds after frame count ⦄ := by
  apply WP.spec_mono (compiler_emit ops law before instruction
    (by have h := room.code; simp only [alloc.vec.Vec.length] at h; omega)
    (by have h := room.sources; simp only [alloc.vec.Vec.length] at h; omega) room.coordinate)
  intro output effect accepted
  exact ⟨effect accepted, room.after_emission (effect accepted)⟩

private theorem branch_copy_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (count : Nat) (room : BranchTotalBounds before frame (count + 1))
    (dst src width : U32) (nonelided : ¬ (width = 0#u32 ∨ src = dst)) :
    runtime.compiler.FunctionCompiler.copy ops before dst src width ⦃ (status, after) =>
      status = .Ok () → Emitted before after (transferInstruction dst src width) ∧
        BranchTotalBounds after frame count ⦄ := by
  apply WP.spec_mono (compiler_copy ops law before dst src width
    (fun same => nonelided (Or.inl same)) (fun same => nonelided (Or.inr same))
    (by have h := room.code; simp only [alloc.vec.Vec.length] at h; omega)
    (by have h := room.sources; simp only [alloc.vec.Vec.length] at h; omega) room.coordinate)
  intro output effect accepted
  exact ⟨effect accepted, room.after_emission (effect accepted)⟩

/-- Normality retains the law-free early rejection paths. Allocation laws and
append bounds are required only after a valid operand interval is established. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.branch.total {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (selected : BranchSelection before depth)
    (normal : ∀ source : U32,
      source.val + (branchWidth selected.frame).val + skip.val = before.height.val →
      (conditional = true ∧ before.before.val = []) ∨
        (Platform.AllocCorrect ops ∧ BranchTotalBounds before selected.frame
          (branchInstructionCount conditional selected.frame source))) :
    runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional ⦃ _ => True ⦄ := by
  rcases selected with ⟨index, frame, lookup, position⟩
  dsimp only at normal
  unfold runtime.compiler.control.FunctionCompiler.branch
  step as ⟨last, lastValue⟩
  step as ⟨converted, convertedValue⟩
  step as ⟨actualIndex, indexValue⟩
  have sameIndex : actualIndex = index := by
    apply UScalar.eq_of_val_eq
    simp only [alloc.vec.Vec.len] at lastValue
    scalar_tac
  subst actualIndex
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨found, foundValue⟩
  have sameFrame : found = frame := foundValue.trans (List.getElem?_eq_some_iff.mp lookup).2
  rw [sameFrame]
  apply WP.spec_bind (Pₘ := fun value => value = branchLoop frame.kind)
  · cases kind : frame.kind <;> simp only [kind, branchLoop, WP.spec_ok]
  intro loop loopEq
  subst loop
  apply WP.spec_bind (Pₘ := fun value => value = branchWidth frame)
  · cases kind : frame.kind <;> simp only [kind, branchLoop, branchWidth, Bool.true_eq,
      Bool.false_eq_true, ite_true, ite_false, WP.spec_ok]
  intro width widthEq
  subst width
  step as ⟨sum, sumValue⟩
  cases sum with
  | none =>
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | some sum =>
    dsimp only at sumValue
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨source, sourceValue⟩
    cases source with
    | none =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | some source =>
      dsimp only at sourceValue
      have sourcePosition : source.val + (branchWidth frame).val + skip.val = before.height.val := by omega
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rcases normal source sourcePosition with ⟨rfl, empty⟩ | ⟨law, demand⟩
      · simp only [Bool.true_eq, ite_true]
        step with compiler_operand_total ops before 1#usize as ⟨answer, contained⟩
        cases answer with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
        | Ok condition =>
          have member := contained condition rfl
          rw [empty] at member
          cases member
      · cases conditional <;>
          simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
        all_goals try
          obtain ⟨answer, operandRun, contained⟩ := WP.spec_imp_exists (compiler_operand_total ops before 1#usize)
          rw [operandRun]
          cases answer
          case' Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          case' Ok condition =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        all_goals by_cases elided : branchWidth frame = 0#u32 ∨ source = frame.height
        all_goals first
          | (have yes : branchWidth frame = 0#u32 ∨ source = frame.height := elided
             have flag : (if branchWidth frame != 0#u32 then Result.ok (source != frame.height)
                 else Result.ok false) = Result.ok false := by
               rcases yes with zero | same
               · rw [zero]
                 simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
               · rw [same]
                 simp only [bne_self_eq_false, ite_self]
             rw [flag]
             simp only [bind_ok, Bool.false_eq_true, ite_false, Bool.true_eq, ite_true]
             simp only [branchInstructionCount, if_pos yes] at demand ⊢)
          | (have no : ¬ (branchWidth frame = 0#u32 ∨ source = frame.height) := elided
             have countNe : branchWidth frame ≠ 0#u32 := fun equal => no (Or.inl equal)
             have sourceNe : source ≠ frame.height := fun equal => no (Or.inr equal)
             have flag : (if branchWidth frame != 0#u32 then Result.ok (source != frame.height)
                 else Result.ok false) = Result.ok true := by
               have a : (branchWidth frame != 0#u32) = true := by simpa only [bne_iff_ne] using countNe
               have b : (source != frame.height) = true := by simpa only [bne_iff_ne] using sourceNe
               rw [a, b]
               rfl
             rw [flag]
             simp only [bind_ok, Bool.false_eq_true, ite_false, Bool.true_eq, ite_true]
             simp only [branchInstructionCount, if_neg no, Bool.true_eq, Bool.false_eq_true,
               ite_true, ite_false] at demand ⊢)
        all_goals try
          have guardCapacity : BranchTotalBounds before frame 3 := demand
          step with branch_emit_total ops law before frame 2 guardCapacity
            (.JumpIfZero condition core.num.U32.MAX) as ⟨answer, afterGuard, effect⟩
          cases answer
          case' Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          case' Ok value => cases value
          all_goals
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            obtain ⟨guardEmission, guardRoom⟩ := effect rfl
            obtain ⟨guardBudget, guardCode, guardSources, rfl, guardAppended, guardRecorded⟩ := guardEmission
            have guardAt : guardCode.val[before.function.code.val.length]? =
                some (.JumpIfZero condition core.num.U32.MAX) := by
              simp only [guardAppended, List.getElem?_concat_length]
        all_goals try
          have copyCapacity : BranchTotalBounds before frame 2 := demand
          step with branch_copy_total ops law before frame 1 copyCapacity
            frame.height source (branchWidth frame) elided as ⟨answer, afterCopy, effect⟩
          cases answer
          case' Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          case' Ok value => cases value
          all_goals
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            obtain ⟨copyEmission, copyRoom⟩ := effect rfl
            obtain ⟨copyBudget, copyCode, copySources, rfl, copyAppended, copyRecorded⟩ := copyEmission
        all_goals try
          step with branch_copy_total ops law _ frame 1 guardRoom
            frame.height source (branchWidth frame) elided as ⟨answer, afterCopy, effect⟩
          cases answer
          case' Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          case' Ok value => cases value
          all_goals
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            obtain ⟨copyEmission, copyRoom⟩ := effect rfl
            have copiedGuard := copyEmission.old_instruction guardAt
            obtain ⟨copyBudget, copyCode, copySources, rfl, copyAppended, copyRecorded⟩ := copyEmission
        all_goals
          step as ⟨current, restore, currentValue, restoreValue⟩
          have currentEq : current = frame := currentValue.trans (List.getElem?_eq_some_iff.mp lookup).2
          rw [currentEq]
          apply WP.spec_bind (Pₘ := fun pair => pair = (frame.kind, branchLoop frame.kind))
          · cases kind : frame.kind <;> simp only [kind, branchLoop, WP.spec_ok]
          intro pair pairEq
          subst pair
          simp only [uncurry_apply_pair]
          cases loopFlag : branchLoop frame.kind <;>
            simp only [loopFlag, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false, bind_ok]
        all_goals try
          have forward : frame.kind ≠ .Loop := by
            intro same
            simp only [same, branchLoop] at loopFlag
            contradiction
          step with budget_push ops law _ frame.fixups _ (demand.fixups forward)
            as ⟨answer, budget, fixups, effect⟩
          rcases effect with ⟨rfl, sameBudget, appendedFixups⟩ | ⟨rfl, unchangedFixups, rejectedBudget⟩
          all_goals try subst budget
          all_goals simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, uncurry_apply_pair, WP.spec_ok]
        all_goals
          first
          | let readyFrames := restore {frame with end_reachable := true, fixups}
          | let readyFrames := restore frame
          first
          | (let ready : runtime.compiler.FunctionCompiler A := {before with
               budget := copyBudget
               function := {before.function with code := copyCode, source_offsets := copySources}
               frames := readyFrames}
             have readyRoom : BranchTotalBounds ready frame 1 := copyRoom.with_frames readyFrames)
          | (let ready : runtime.compiler.FunctionCompiler A := {before with frames := readyFrames}
             have readyRoom : BranchTotalBounds ready frame 1 := demand.with_frames readyFrames)
          first
          | (have isLoop : branchLoop frame.kind = true := loopFlag
             let target := frame.start_pc)
          | let target := core.num.U32.MAX
          first
          | (have one : BranchTotalBounds before frame 1 := demand
             let instruction := runtime.bytecode.Instr.JumpIfNonZero condition target)
          | let instruction := runtime.bytecode.Instr.Jump target
          step with branch_emit_total ops law ready frame 0 readyRoom instruction
            as ⟨answer, afterJump, effect⟩
          cases answer
          case' Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          case' Ok value => cases value
          all_goals
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
        all_goals
          obtain ⟨jumpEmission, jumpRoom⟩ := effect rfl
          have finalGuard := jumpEmission.old_instruction copiedGuard
          obtain ⟨finalBudget, finalCode, finalSources, rfl, finalAppended, finalRecorded⟩ := jumpEmission
          let emitted : runtime.compiler.FunctionCompiler A := {ready with
            budget := finalBudget
            function := {ready.function with code := finalCode, source_offsets := finalSources}}
          step with compiler_pc ops emitted
            as ⟨answer, afterPc, sameFunction, positionPc, framePc⟩
          cases answer
          case' Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
          case' Ok target =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            have guardLookup : afterPc.function.code.val[(alloc.vec.Vec.len before.function.code).val]? =
                some (BranchKind.instruction (.zero condition) core.num.U32.MAX) := by
              rw [sameFunction]
              simpa only [emitted, alloc.vec.Vec.len, Usize.ofNatCore_val_eq, BranchKind.instruction] using finalGuard
            step with runtime.compiler.control.FunctionCompiler.patch.available ops afterPc
              (alloc.vec.Vec.len before.function.code) (.zero condition) core.num.U32.MAX target guardLookup
              as ⟨answer, afterPatch, accepted, patched⟩
            rw [accepted]
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]

end Itasca.Compiler

end

/-! ## BranchEffects -/

section

open Itasca.Representation

/-! Pure projections from canonical branch traces. These recover selected
operand intervals and exact instruction/frame publication without unfolding the
compiler's branch implementation. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

theorem branch_index {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length) :
    (do
      let last ← alloc.vec.Vec.len compiler.frames - 1#usize
      let d ← lift (UScalar.cast .Usize depth)
      let selected ← last - d
      let found ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) compiler.frames selected
      Result.ok (selected, found)) ⦃ out => out = (index, frame) ⦄ := by
  step as ⟨last, hlast⟩
  step as ⟨d, hd⟩
  step as ⟨actualIndex, hindex⟩
  have indexEq : actualIndex = index := by apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len] at hlast; scalar_tac
  subst actualIndex
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨found, hfound⟩
  have foundEq : found = frame := by simpa [List.getElem?_eq_getElem inBounds, hfound] using lookup
  simp [foundEq]

/-- Supplied selection and source coordinates identify the trace's checked
prologue, including for an ordinary error in a later phase. -/
theorem BranchEffect.condition {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip : U32} {conditional : Bool}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : BranchEffect ops before after depth skip conditional status)
    (selected : BranchSelection before depth) (source : U32)
    (position : source.val + (branchWidth selected.frame).val + skip.val = before.height.val) :
    BranchCondition ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) conditional status := by
  obtain ⟨last, converted, index, frame, lastRun, convertedRun, indexRun, frameRun, tail⟩ := effect
  have found := branch_index before selected.frame selected.index depth selected.lookup selected.position
  rw [lastRun, bind_ok, convertedRun, bind_ok, indexRun, bind_ok, frameRun, bind_ok, WP.spec_ok] at found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj found
  obtain ⟨sum, sumRun, tail⟩ := tail
  have sumFacts : lift (U32.checked_add skip (branchWidth selected.frame)) ⦃ value =>
      match value with
      | none => U32.max < skip.val + (branchWidth selected.frame).val
      | some value => value.val = skip.val + (branchWidth selected.frame).val ⦄ := by
    step as ⟨value, facts⟩
    cases value <;> dsimp only at facts ⊢
    · exact facts
    · exact facts.2.1
  rw [sumRun, WP.spec_ok] at sumFacts
  cases sum with
  | none =>
    dsimp only at sumFacts
    have heightBound : before.height.val ≤ U32.max := by scalar_tac
    omega
  | some sum =>
    dsimp only at sumFacts
    obtain ⟨actualSource, sourceRun, tail⟩ := tail
    have sourceFacts : lift (U32.checked_sub before.height sum) ⦃ value =>
        match value with
        | none => before.height.val < sum.val
        | some value => value.val + sum.val = before.height.val ⦄ := by
      step as ⟨value, facts⟩
      cases value <;> dsimp only at facts ⊢
      · exact facts
      · omega
    rw [sourceRun, WP.spec_ok] at sourceFacts
    cases actualSource with
    | none =>
      dsimp only at sourceFacts
      omega
    | some actualSource =>
      dsimp only at sourceFacts
      have same : actualSource = source := by apply UScalar.eq_of_val_eq; omega
      subst actualSource
      exact tail

/-- The selected frame either stays unchanged (loop) or records its pending
forward jump and end reachability. -/
def BranchFrameUpdate {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (frame : runtime.compiler.Frame) (site : Usize) : Prop :=
  if branchLoop frame.kind then after.frames = before.frames
  else ∃ fixups, after.frames.val = before.frames.val.set index.val {frame with end_reachable := true, fixups} ∧
    fixups.val = frame.fixups.val ++ [site]

/-- A loop names its existing start; a forward branch leaves a pending target. -/
def branchTarget (frame : runtime.compiler.Frame) : U32 :=
  if branchLoop frame.kind then frame.start_pc else core.num.U32.MAX

/-- A successful jump without a guard patch is one exact emission. -/
theorem BranchJumpCall.unpatched {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction : runtime.bytecode.Instr}
    (effect : BranchJumpCall ops before after instruction none (.Ok ())) (law : Platform.AllocCorrect ops) :
    EmittedExact before after instruction := by
  obtain ⟨answer, middle, emitted, tail⟩ := effect
  cases answer with
  | Err error => cases tail.1
  | Ok value =>
    cases value
    obtain ⟨_, rfl⟩ := tail
    exact ((runtime.compiler.FunctionCompiler.emit.inv ops before _ instruction _ emitted).2 law).2 rfl

/-- Successful guarded publication first emits its jump and then patches the
previous guard to the final PC. -/
theorem BranchJumpCall.guarded {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction : runtime.bytecode.Instr}
    {site : Usize} {condition : U32}
    (effect : BranchJumpCall ops before after instruction (some site) (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (atGuard : before.function.code.val[site.val]? = some (.JumpIfZero condition core.num.U32.MAX)) :
    ∃ middle target, EmittedExact before middle instruction ∧
      target.val = middle.function.code.val.length ∧
      Patched middle after site.val (.JumpIfZero condition target) := by
  obtain ⟨answer, middle, emitted, tail⟩ := effect
  cases answer with
  | Err error => cases tail.1
  | Ok value =>
    cases value
    have emission := ((runtime.compiler.FunctionCompiler.emit.inv ops before middle instruction _ emitted).2 law).2 rfl
    obtain ⟨pcAnswer, afterPc, pcRun, tail⟩ := tail
    cases pcAnswer with
    | Err error => cases tail.1
    | Ok target =>
      have pc := compiler_pc ops middle
      rw [pcRun, WP.spec_ok] at pc
      have targetPosition := pc.2.1 target rfl
      have bounded : middle.function.code.length ≤ U32.max := by
        simp only [alloc.vec.Vec.length]
        scalar_tac
      have successfulPc := compiler_pc_available ops middle bounded
      rw [pcRun, WP.spec_ok] at successfulPc
      have same : afterPc = middle := successfulPc.1
      subst afterPc
      have patched := runtime.compiler.control.FunctionCompiler.patch.available ops middle site
        (.zero condition) core.num.U32.MAX target (emission.emitted.old_instruction atGuard)
      rw [tail, WP.spec_ok] at patched
      exact ⟨middle, target, emission, targetPosition, patched.2⟩

/-- A successful publication has the exact selected-frame effect, and retains
its final jump/patch continuation for subsequent projections. -/
theorem BranchPublication.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index : Usize}
    {conditional copying : Bool} {condition : U32} {guard : Option Usize}
    (effect : BranchPublication ops before after index conditional copying condition guard (.Ok ()))
    (law : Platform.AllocCorrect ops) (frame : runtime.compiler.Frame)
    (lookup : before.frames.val[index.val]? = some frame) :
    ∃ ready frames, ready = {before with frames} ∧
      BranchFrameUpdate before ready index frame (alloc.vec.Vec.len before.function.code) ∧
      BranchJumpCall ops ready after (branchJump conditional copying condition (branchTarget frame)) guard (.Ok ()) := by
  obtain ⟨current, restore, read, tail⟩ := effect
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  have readSpec : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
      before.frames index ⦃ (value, back) => value = frame ∧
        ∀ replacement, (back replacement).val = before.frames.val.set index.val replacement ⦄ := by
    step as ⟨value, back, found, replaced⟩
    have same : value = frame := found.trans (List.getElem?_eq_some_iff.mp lookup).2
    exact ⟨same, fun replacement => by rw [replaced]; exact alloc.vec.Vec.set_val_eq _ _ _⟩
  rw [read, WP.spec_ok] at readSpec
  have same := readSpec.1
  have restored := readSpec.2
  subst current
  cases loop : branchLoop frame.kind <;>
    simp only [loop, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at tail
  · obtain ⟨answer, budget, fixups, pushed, tail⟩ := tail
    cases answer with
    | Err error => cases tail.1
    | Ok value =>
      cases value
      have pushedEffect := budget_push_success ops law before.budget budget frame.fixups fixups
        (alloc.vec.Vec.len before.function.code) pushed
      have sameBudget := pushedEffect.1
      subst budget
      refine ⟨_, restore {frame with end_reachable := true, fixups}, rfl, ?_, ?_⟩
      · simp only [BranchFrameUpdate, loop, Bool.false_eq_true, ite_false]
        exact ⟨fixups, restored _, pushedEffect.2⟩
      · simpa only [branchTarget, loop, Bool.false_eq_true, ite_false] using tail
  · have original : restore frame = before.frames := by
      apply alloc.vec.Vec.ext
      rw [restored]
      have found := (List.getElem?_eq_some_iff.mp lookup).2
      simpa only [← found] using List.set_getElem_self inBounds
    refine ⟨_, restore frame, rfl, ?_, ?_⟩
    · simp only [BranchFrameUpdate, loop, Bool.true_eq, ite_true]
      exact original
    · simpa only [branchTarget, loop, Bool.true_eq, ite_true] using tail

/-- The copy/publication portion retains its exact optional transfer and the
final jump continuation, sharing the proof across forward and loop targets. -/
theorem BranchCopy.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    {conditional copying : Bool} {condition : U32} {guard : Option Usize}
    (selected : BranchSelection before depth) (source : U32)
    (effect : BranchCopy ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) conditional copying condition guard (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (nonelided : copying = true → ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height)) :
    ∃ middle ready frames,
      (if copying then EmittedExact before middle
        (transferInstruction selected.frame.height source (branchWidth selected.frame)) else middle = before) ∧
      ready = {middle with frames} ∧
      BranchFrameUpdate middle ready selected.index selected.frame (alloc.vec.Vec.len middle.function.code) ∧
      BranchJumpCall ops ready after
        (branchJump conditional copying condition (branchTarget selected.frame)) guard (.Ok ()) := by
  cases copying <;> simp only [BranchCopy, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at effect ⊢
  · obtain ⟨ready, frames, same, updated, jump⟩ := effect.success law selected.frame selected.lookup
    exact ⟨before, ready, frames, rfl, same, updated, jump⟩
  · obtain ⟨answer, middle, copied, tail⟩ := effect
    cases answer with
    | Err error => cases tail.1
    | Ok value =>
      cases value
      have exactCopy : EmittedExact before middle
          (transferInstruction selected.frame.height source (branchWidth selected.frame)) := by
        rcases runtime.compiler.FunctionCompiler.copy.inv ops before middle selected.frame.height source
            (branchWidth selected.frame) (.Ok ()) copied with ⟨elided, _, _⟩ | ⟨_, _, emitted⟩
        · exact False.elim (nonelided rfl elided)
        · exact ((runtime.compiler.FunctionCompiler.emit.inv ops before middle _ _ emitted).2 law).2 rfl
      have lookup : middle.frames.val[selected.index.val]? = some selected.frame := by
        obtain ⟨used, code, sources, rfl, _, _, _⟩ := exactCopy
        exact selected.lookup
      obtain ⟨ready, frames, same, updated, jump⟩ := tail.success law selected.frame lookup
      exact ⟨middle, ready, frames, exactCopy, same, updated, jump⟩

def BranchCodeBound {A : Type} (before after : runtime.compiler.FunctionCompiler A) (count : Nat) : Prop :=
  before.function.code.val.length ≤ after.function.code.val.length ∧
    after.function.code.val.length ≤ before.function.code.val.length + count

theorem BranchCodeBound.same {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (same : after.function.code.val.length = before.function.code.val.length) : BranchCodeBound before after 0 := by
  unfold BranchCodeBound
  rw [same]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem BranchCodeBound.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A} {first second}
    (head : BranchCodeBound before middle first) (tail : BranchCodeBound middle after second) :
    BranchCodeBound before after (first + second) := by
  obtain ⟨h1, h2⟩ := head
  obtain ⟨t1, t2⟩ := tail
  constructor <;> omega

theorem BranchCodeBound.weaken {A : Type} {before after : runtime.compiler.FunctionCompiler A} {small large}
    (effect : BranchCodeBound before after small) (bound : small ≤ large) : BranchCodeBound before after large := by
  obtain ⟨lower, upper⟩ := effect
  constructor <;> omega

private theorem branch_emit_code_bound {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr) (status)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    BranchCodeBound before after 1 := by
  have growth := ((runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status called).2 law).1
  rcases growth with same | added <;> unfold BranchCodeBound
  · rw [same]; omega
  · rw [added, List.length_append, List.length_singleton]; omega

private theorem branch_copy_code_bound {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32) (status)
    (called : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    BranchCodeBound before after 1 := by
  rcases runtime.compiler.FunctionCompiler.copy.inv ops before after dst src count status called with ⟨_, _, same⟩ | ⟨_, _, emitted⟩
  · rw [same]; exact (BranchCodeBound.same rfl).weaken (by omega)
  · exact branch_emit_code_bound ops law _ _ _ _ emitted

theorem BranchPatch.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {guard status}
    (effect : BranchPatch ops before after guard status) : BranchCodeBound before after 0 := by
  cases guard with
  | none => rw [effect.2]; exact .same rfl
  | some site =>
    obtain ⟨answer, middle, called, rest⟩ := effect
    have pc := compiler_pc ops before
    rw [called, WP.spec_ok] at pc
    have same : middle.function = before.function := pc.1
    have head : BranchCodeBound before middle 0 := .same (by rw [same])
    apply head.trans (second := 0)
    cases answer with
    | Err error => rw [rest.2]; exact .same rfl
    | Ok target =>
      apply BranchCodeBound.same
      rcases compiler_patch_cases ops middle after site target status rest with unchanged | ⟨instruction, code, frame, contents⟩
      · rw [unchanged]
      · rw [frame]
        simp only [contents, List.length_set]

theorem BranchJumpCall.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard status}
    (effect : BranchJumpCall ops before after instruction guard status) (law : Platform.AllocCorrect ops) : BranchCodeBound before after 1 := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  have head := branch_emit_code_bound ops law _ _ _ _ called
  cases answer with
  | Err error => rw [rest.2]; exact head
  | Ok value => exact head.trans rest.code_bound

theorem BranchPublication.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard status}
    (effect : BranchPublication ops before after index conditional copying condition guard status) (law : Platform.AllocCorrect ops) : BranchCodeBound before after 1 := by
  obtain ⟨frame, restore, _, rest⟩ := effect
  split at rest
  · have bound := rest.code_bound law
    exact bound
  · obtain ⟨answer, budget, fixups, _, rest⟩ := rest
    cases answer with
    | Err error => rw [rest.2]; exact (BranchCodeBound.same rfl).weaken (by omega)
    | Ok value =>
      have bound := rest.code_bound law
      exact bound

theorem BranchCopy.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard status}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard status) (law : Platform.AllocCorrect ops) : BranchCodeBound before after 2 := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    have head := branch_copy_code_bound ops law _ _ _ _ _ _ called
    cases answer with
    | Err error => rw [rest.2]; exact head.weaken (by omega)
    | Ok value => exact head.trans (rest.code_bound law)
  · exact (effect.code_bound law).weaken (by omega)

theorem BranchTransfer.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition status}
    (effect : BranchTransfer ops before after index dst src count conditional condition status) (law : Platform.AllocCorrect ops) :
    BranchCodeBound before after (if conditional then 3 else 2) := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · rename_i guarded
    have live : conditional = true := (Bool.and_eq_true_iff.mp guarded).1
    simp only [live, ite_true]
    obtain ⟨answer, middle, called, rest⟩ := effect
    have head := branch_emit_code_bound ops law _ _ _ _ called
    cases answer with
    | Err error => rw [rest.2]; exact head.weaken (by omega)
    | Ok value => exact head.trans (rest.code_bound law)
  · apply (effect.code_bound law).weaken
    split <;> omega

theorem BranchCondition.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional status}
    (effect : BranchCondition ops before after index dst src count conditional status) (law : Platform.AllocCorrect ops) :
    BranchCodeBound before after (if conditional then 3 else 2) := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => rw [rest.2]; exact (BranchCodeBound.same rfl).weaken (Nat.zero_le _)
    | Ok value => exact rest.code_bound law
  · exact effect.code_bound law

theorem BranchSource.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional status}
    (effect : BranchSource ops before after index frame skip conditional status) (law : Platform.AllocCorrect ops) :
    BranchCodeBound before after (if conditional then 3 else 2) := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => rw [rest.2]; exact (BranchCodeBound.same rfl).weaken (Nat.zero_le _)
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => rw [rest.2]; exact (BranchCodeBound.same rfl).weaken (Nat.zero_le _)
    | some src => exact rest.code_bound law

theorem BranchEffect.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional status}
    (effect : BranchEffect ops before after depth skip conditional status) (law : Platform.AllocCorrect ops) :
    BranchCodeBound before after (if conditional then 3 else 2) := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.code_bound law

/-- Exact code and frame publication for a branch whose final jump needs no
separate guard patch. -/
theorem BranchCopy.unpatched_success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    {conditional copying : Bool} {condition : U32}
    (selected : BranchSelection before depth) (source : U32)
    (effect : BranchCopy ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) conditional copying condition none (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (nonelided : copying = true → ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height)) :
    ∃ site,
      after.function.code.val = before.function.code.val ++
        (if copying then [transferInstruction selected.frame.height source (branchWidth selected.frame)] else []) ++
        [branchJump conditional copying condition (branchTarget selected.frame)] ∧
      site.val = before.function.code.val.length + (if copying then 1 else 0) ∧
      BranchFrameUpdate before after selected.index selected.frame site := by
  obtain ⟨middle, ready, frames, transferred, rfl, updated, jump⟩ :=
    effect.success selected source law nonelided
  have emitted := jump.unpatched law
  obtain ⟨used, code, sources, rfl, _, appended, _⟩ := emitted
  refine ⟨alloc.vec.Vec.len middle.function.code, ?_, ?_, ?_⟩
  · cases copying <;> simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at transferred ⊢
    · subst middle
      simpa only [List.append_nil] using appended
    · obtain ⟨copyUsed, copyCode, copySources, rfl, _, copied, _⟩ := transferred
      simpa only [copied] using appended
  · cases copying <;> simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at transferred ⊢
    · subst middle
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, Nat.add_zero]
    · obtain ⟨copyUsed, copyCode, copySources, rfl, _, copied, _⟩ := transferred
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, copied, List.length_append,
        List.length_cons, List.length_nil]
  · cases copying <;> simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at transferred
    · subst middle
      exact updated
    · obtain ⟨copyUsed, copyCode, copySources, rfl, _, _, _⟩ := transferred
      exact updated

/-- The nonelided-copy flag is false precisely in the two elision cases. -/
theorem branch_copy_flag_false (count source destination : U32)
    (elided : count = 0#u32 ∨ source = destination) :
    ((count != 0#u32) && (source != destination)) = false := by
  rcases elided with zero | same
  · simp only [zero, bne_self_eq_false, Bool.false_and]
  · simp only [same, bne_self_eq_false, Bool.and_false]

theorem branch_copy_flag_true (count source destination : U32)
    (nonelided : ¬ (count = 0#u32 ∨ source = destination)) :
    ((count != 0#u32) && (source != destination)) = true := by
  simp only [Bool.and_eq_true, bne_iff_ne]
  exact ⟨fun equal => nonelided (Or.inl equal), fun equal => nonelided (Or.inr equal)⟩

/-- A conditional transfer emits a guard, one copy, and its jump, then retargets
the guard to the point immediately after those three instructions. -/
theorem BranchTransfer.guarded_success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32} {condition : U32}
    (selected : BranchSelection before depth) (source : U32)
    (effect : BranchTransfer ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) true condition (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (nonelided : ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height)) :
    ∃ resume site,
      after.function.code.val = before.function.code.val ++
        [.JumpIfZero condition resume,
          transferInstruction selected.frame.height source (branchWidth selected.frame),
          .Jump (branchTarget selected.frame)] ∧
      site.val = before.function.code.val.length + 2 ∧
      BranchFrameUpdate before after selected.index selected.frame site ∧
      resume.val = before.function.code.val.length + 3 := by
  have flag := branch_copy_flag_true (branchWidth selected.frame) source selected.frame.height nonelided
  simp only [BranchTransfer, flag, Bool.true_and, Bool.true_eq, ite_true] at effect
  obtain ⟨answer, guardState, guardRun, tail⟩ := effect
  cases answer with
  | Err error => cases tail.1
  | Ok value =>
    cases value
    have guardEmission := ((runtime.compiler.FunctionCompiler.emit.inv ops before guardState _ _ guardRun).2 law).2 rfl
    obtain ⟨guardUsed, guardCode, guardSources, rfl, _, guardAppended, _⟩ := guardEmission
    have guardAt : guardCode.val[(alloc.vec.Vec.len before.function.code).val]? =
        some (.JumpIfZero condition core.num.U32.MAX) := by
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, guardAppended, List.getElem?_concat_length]
    obtain ⟨middle, ready, frames, copyEmission, rfl, updated, jump⟩ :=
      tail.success (show BranchSelection {before with
        budget := {before.budget with instructions := guardUsed}
        function := {before.function with code := guardCode, source_offsets := guardSources}} depth from
          ⟨selected.index, selected.frame, selected.lookup, selected.position⟩) source law (fun _ => nonelided)
    change EmittedExact _ middle _ at copyEmission
    have copiedGuard := copyEmission.emitted.old_instruction guardAt
    obtain ⟨copyUsed, copyCode, copySources, rfl, _, copyAppended, _⟩ := copyEmission
    obtain ⟨jumpState, resume, jumpEmission, resumePosition, patched⟩ := jump.guarded law copiedGuard
    obtain ⟨jumpUsed, jumpCode, jumpSources, rfl, _, jumpAppended, _⟩ := jumpEmission
    obtain ⟨patchedCode, rfl, patchedValues⟩ := patched
    simp only [branchJump, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false] at jumpAppended
    refine ⟨resume, alloc.vec.Vec.len copyCode, ?_, ?_, ?_, ?_⟩
    · change patchedCode.val = _
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq] at patchedValues
      rw [patchedValues, jumpAppended, copyAppended, guardAppended]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [List.set_append_right _ _ (Nat.le_refl _)]
      simp only [Nat.sub_self, List.set_cons_zero]
    · simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, copyAppended, guardAppended,
        List.length_append, List.length_cons, List.length_nil, Nat.add_assoc]
    · exact updated
    · simpa only [jumpAppended, copyAppended, guardAppended, List.length_append,
        List.length_cons, List.length_nil, Nat.add_assoc] using resumePosition

/-- Supplied conditional-operand evidence identifies the transfer trace. -/
theorem BranchEffect.transfer {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip : U32} {conditional : Bool}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : BranchEffect ops before after depth skip conditional status)
    (selected : BranchSelection before depth) (source : U32)
    (position : source.val + (branchWidth selected.frame).val + skip.val = before.height.val)
    (condition : U32) (ready : conditional = true →
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition)) :
    BranchTransfer ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) conditional (if conditional then condition else 0#u32) status := by
  have tail := effect.condition selected source position
  cases conditional <;> simp only [BranchCondition, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at tail ⊢
  · exact tail
  · obtain ⟨answer, called, tail⟩ := tail
    rw [ready rfl] at called
    have same : answer = .Ok condition := (Result.ok_injective called).symm
    subst answer
    exact tail

/-- The exact instruction suffix of successful branch lowering. -/
def branchOutput (conditional : Bool) (frame : runtime.compiler.Frame) (source condition resume : U32) :
    List runtime.bytecode.Instr :=
  if branchWidth frame = 0#u32 ∨ source = frame.height then
    [branchJump conditional false condition (branchTarget frame)]
  else if conditional then
    [.JumpIfZero condition resume, transferInstruction frame.height source (branchWidth frame), .Jump (branchTarget frame)]
  else [transferInstruction frame.height source (branchWidth frame), .Jump (branchTarget frame)]

/-- Successful traces recover the exact code suffix, jump site, and selected
frame update. A conditional transfer also identifies its guard's final target. -/
theorem BranchEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip : U32} {conditional : Bool}
    (effect : BranchEffect ops before after depth skip conditional (.Ok ()))
    (selected : BranchSelection before depth) (source : U32)
    (position : source.val + (branchWidth selected.frame).val + skip.val = before.height.val)
    (condition : U32) (ready : conditional = true →
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition))
    (law : Platform.AllocCorrect ops) :
    ∃ resume site,
      after.function.code.val = before.function.code.val ++ branchOutput conditional selected.frame source condition resume ∧
      site.val = before.function.code.val.length + (branchInstructionCount conditional selected.frame source - 1) ∧
      BranchFrameUpdate before after selected.index selected.frame site ∧
      (conditional = true → ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height) →
        resume.val = before.function.code.val.length + 3) := by
  have trace := effect.transfer selected source position condition ready
  cases conditional <;> simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at trace ⊢
  all_goals by_cases elided : branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height
  all_goals first
    | (have yes : branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height := elided
       have flag := branch_copy_flag_false (branchWidth selected.frame) source selected.frame.height yes
       simp only [BranchTransfer, flag, Bool.and_false, Bool.false_and, Bool.true_and,
         Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at trace
       obtain ⟨site, code, sitePosition, updated⟩ :=
         trace.unpatched_success selected source law (by intro impossible; cases impossible)
       refine ⟨0#u32, site, ?_, ?_, updated, ?_⟩
       · simpa only [branchOutput, if_pos yes, branchJump, Bool.not_false, Bool.and_true,
           Bool.true_eq, Bool.false_eq_true, ite_true, ite_false, List.append_nil] using code
       · simpa only [branchInstructionCount, if_pos yes, Bool.false_eq_true, ite_false] using sitePosition
       · intro _ different
         exact False.elim (different yes))
    | (have no : ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height) := elided
       first
       | (obtain ⟨resume, site, code, sitePosition, updated, resumePosition⟩ :=
             trace.guarded_success selected source law no
          refine ⟨resume, site, ?_, ?_, updated, fun _ _ => resumePosition⟩
          · simpa only [branchOutput, if_neg no, Bool.true_eq, ite_true] using code
          · simpa only [branchInstructionCount, if_neg no, Bool.true_eq, ite_true] using sitePosition)
       | (have flag := branch_copy_flag_true (branchWidth selected.frame) source selected.frame.height no
          simp only [BranchTransfer, flag, Bool.false_and, Bool.false_eq_true, ite_false] at trace
          obtain ⟨site, code, sitePosition, updated⟩ := trace.unpatched_success selected source law (fun _ => no)
          refine ⟨0#u32, site, ?_, ?_, updated, ?_⟩
          · simpa only [branchOutput, if_neg no, branchJump, Bool.not_true, Bool.false_and,
              Bool.false_eq_true, ite_false, Bool.true_eq, ite_true, List.append_assoc,
              List.cons_append, List.nil_append] using code
          · simpa only [branchInstructionCount, if_neg no, Bool.false_eq_true, ite_false,
              Bool.true_eq, ite_true] using sitePosition
          · intro impossible
            cases impossible))

def BranchSourceTrace {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  BranchFrame before after ∧ ∃ count,
    after.function.code.val.length = before.function.code.val.length + count ∧
    after.function.source_offsets.val.map UScalar.val = before.function.source_offsets.val.map UScalar.val ++
      List.replicate count (before.function.body_start.val + before.next_source.val)

theorem BranchSourceTrace.refl {A : Type} (before : runtime.compiler.FunctionCompiler A) : BranchSourceTrace before before := by
  exact ⟨rfl, 0, rfl, by simp only [List.replicate_zero, List.append_nil]⟩

theorem BranchSourceTrace.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : BranchSourceTrace before middle) (second : BranchSourceTrace middle after) : BranchSourceTrace before after := by
  obtain ⟨firstFrame, n, firstCode, firstSources⟩ := first
  obtain ⟨secondFrame, m, secondCode, secondSources⟩ := second
  refine ⟨firstFrame.trans secondFrame, n + m, by omega, ?_⟩
  have origin : middle.function.body_start.val + middle.next_source.val = before.function.body_start.val + before.next_source.val := by
    rw [firstFrame]
  simp only [secondSources, firstSources, origin, List.replicate_add, List.append_assoc]

theorem EmittedExact.branch_sources {A : Type} {before after : runtime.compiler.FunctionCompiler A} {instruction}
    (effect : EmittedExact before after instruction) : BranchSourceTrace before after := by
  obtain ⟨used, code, sources, rfl, _, appended, mapped⟩ := effect
  refine ⟨rfl, 1, ?_, ?_⟩
  · simp only [appended, List.length_append, List.length_singleton]
  · simpa only [List.replicate_succ, List.replicate_zero] using mapped

private theorem branch_pc_source_trace {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (status)
    (called : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) : BranchSourceTrace before after := by
  have post := compiler_pc ops before
  rw [called, WP.spec_ok] at post
  obtain ⟨budget, same⟩ := post.2.2
  change after = {before with budget} at same
  rw [same]
  exact ⟨rfl, 0, rfl, by simp only [List.replicate_zero, List.append_nil]⟩

private theorem branch_patch_source_trace {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (site : Usize) (target : U32) (status)
    (called : runtime.compiler.control.FunctionCompiler.patch ops before site target = .ok (status, after)) : BranchSourceTrace before after := by
  rcases compiler_patch_cases ops before after site target status called with same | ⟨instruction, code, same, contents⟩
  · rw [same]; exact .refl _
  · rw [same]
    refine ⟨rfl, 0, ?_, ?_⟩
    · simp only [contents, List.length_set, Nat.add_zero]
    · simp only [List.replicate_zero, List.append_nil]

theorem BranchPatch.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {guard}
    (effect : BranchPatch ops before after guard (.Ok ())) : BranchSourceTrace before after := by
  cases guard with
  | none => rw [effect.2]; exact .refl _
  | some site =>
    obtain ⟨answer, middle, called, rest⟩ := effect
    have head := branch_pc_source_trace ops _ _ _ called
    cases answer with
    | Err error => cases rest.1
    | Ok target => exact head.trans (branch_patch_source_trace ops _ _ _ _ _ rest)

theorem BranchJumpCall.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard}
    (effect : BranchJumpCall ops before after instruction guard (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  cases answer with
  | Err error => cases rest.1
  | Ok value =>
    cases value
    exact (((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl).branch_sources.trans rest.source_trace

theorem BranchPublication.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard}
    (effect : BranchPublication ops before after index conditional copying condition guard (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  obtain ⟨frame, restore, _, rest⟩ := effect
  split at rest
  · have trace := rest.source_trace law
    exact trace
  · obtain ⟨answer, budget, fixups, _, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      have trace := rest.source_trace law
      exact trace

theorem BranchCopy.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      have copied := (runtime.compiler.FunctionCompiler.copy.inv ops before middle dst src count (.Ok ()) called).exact law rfl
      rcases copied with same | emitted
      · subst middle
        exact rest.source_trace law
      · exact emitted.branch_sources.trans (rest.source_trace law)
  · exact effect.source_trace law

theorem BranchTransfer.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition}
    (effect : BranchTransfer ops before after index dst src count conditional condition (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      exact (((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl).branch_sources.trans (rest.source_trace law)
  · exact effect.source_trace law

theorem BranchCondition.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional}
    (effect : BranchCondition ops before after index dst src count conditional (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value => exact rest.source_trace law
  · exact effect.source_trace law

theorem BranchSource.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional}
    (effect : BranchSource ops before after index frame skip conditional (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => cases rest.1
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => cases rest.1
    | some src => exact rest.source_trace law

theorem BranchEffect.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional}
    (effect : BranchEffect ops before after depth skip conditional (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.source_trace law

theorem BranchJumpCall.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard}
    (effect : BranchJumpCall ops before after instruction guard (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  cases answer with
  | Err error => cases rest.1
  | Ok value =>
    cases value
    have emitted := (((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl).branch_sources
    obtain ⟨_, count, code, _⟩ := emitted
    have one : middle.function.code.val = before.function.code.val ++ [instruction] := by
      obtain ⟨used, code, sources, same, _, appended, mapped⟩ :=
        ((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl
      rw [same]
      exact appended
    obtain ⟨lower, upper⟩ := rest.code_bound
    simp only [one, List.length_append, List.length_singleton] at lower upper
    omega

theorem BranchPublication.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard}
    (effect : BranchPublication ops before after index conditional copying condition guard (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  obtain ⟨frame, restore, _, rest⟩ := effect
  split at rest
  · have trace := rest.code_strict law
    exact trace
  · obtain ⟨answer, budget, fixups, _, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      have trace := rest.code_strict law
      exact trace

theorem BranchCopy.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      have copied := (runtime.compiler.FunctionCompiler.copy.inv ops before middle dst src count (.Ok ()) called).exact law rfl
      rcases copied with same | emitted
      · subst middle
        exact rest.code_strict law
      · have growth := (emitted.branch_sources).2
        obtain ⟨count, code, _⟩ := growth
        have strict := rest.code_strict law
        omega
  · exact effect.code_strict law

theorem BranchTransfer.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition}
    (effect : BranchTransfer ops before after index dst src count conditional condition (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      obtain ⟨_, count, code, _⟩ := (((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl).branch_sources
      have strict := rest.code_strict law
      omega
  · exact effect.code_strict law

theorem BranchCondition.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional}
    (effect : BranchCondition ops before after index dst src count conditional (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value => exact rest.code_strict law
  · exact effect.code_strict law

theorem BranchSource.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional}
    (effect : BranchSource ops before after index frame skip conditional (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => cases rest.1
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => cases rest.1
    | some src => exact rest.code_strict law

theorem BranchEffect.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional}
    (effect : BranchEffect ops before after depth skip conditional (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.code_strict law

end Itasca.Compiler

end

/-! ## ExitContracts -/

section

/-!
Proofs for Runtime / Compiler / Local / Lowering / Control.

This module collects UnreachableContracts, ReturnContracts.
Each section documents its contracts and consumers.
-/

/-! ## UnreachableContracts -/

section

/-! Contracts for the unreachable callback. A live callback emits the trap
before marking the compiler dead and observing the validator stack; a dead
callback only observes. The effect retains partial emission failures and the
final observation witness for metadata, coordinates, and safety consumers. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

inductive UnreachableEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | dead {status after} (dead : before.reachable = false)
      (observed : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
      UnreachableEffect ops before state status after
  | rejected {error after} (live : before.reachable = true)
      (emitted : runtime.compiler.FunctionCompiler.emit ops before .Unreachable = .ok (.Err error, after)) :
      UnreachableEffect ops before state (.Err error) after
  | emitted {middle status after} (live : before.reachable = true)
      (emitted : runtime.compiler.FunctionCompiler.emit ops before .Unreachable = .ok (.Ok (), middle))
      (observed : runtime.compiler.FunctionCompiler.observe ops {middle with reachable := false} state = .ok (status, after)) :
      UnreachableEffect ops before state status after

/-- Dead input bypasses emission entirely. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.dead
    {A : Type} (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : before.reachable = false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state =
      runtime.compiler.FunctionCompiler.observe ops before state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable,
    dead, Bool.false_eq_true, ite_false]

/-- Normal returns retain their actual emission and observation evidence. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv
    {A : Type} (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state = .ok (status, after)) :
    UnreachableEffect ops before state status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at called
  cases live : before.reachable with
  | false =>
    simp only [live, Bool.false_eq_true, ite_false] at called
    exact .dead live called
  | true =>
    simp only [live, ite_true] at called
    obtain ⟨⟨reply, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ called
    cases reply with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      exact .rejected live emitted
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      exact .emitted live emitted rest

/-- Successful returns observe a compiler whose reachability is false. -/
theorem UnreachableEffect.observation {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    (effect : UnreachableEffect ops before state (.Ok ()) after) :
    ∃ middle, middle.reachable = false ∧
      runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  cases effect with
  | dead dead observed => exact ⟨_, dead, observed⟩
  | emitted live emitted observed => exact ⟨_, rfl, observed⟩

/-- Fields permitted to change on a normal unreachable-callback return. -/
def UnreachableFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget
    before := after.before
    height := after.height
    next_source := after.next_source
    reachable := after.reachable
    function := {before.function with
      code := after.function.code
      source_offsets := after.function.source_offsets
      max_stack := after.function.max_stack
      slot_count := after.function.slot_count}}

theorem UnreachableEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : UnreachableEffect ops before state status after) : UnreachableFrame before after := by
  cases effect with
  | dead dead observed =>
    have frame := compiler_observe_frame_raw ops before state status after observed
    unfold UnreachableFrame
    rw [frame]
  | rejected live emitted =>
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after .Unreachable _ emitted).1
    unfold UnreachableFrame
    rw [frame]
  | @emitted middle _ _ live emitted observed =>
    have emission := (runtime.compiler.FunctionCompiler.emit.inv ops before middle .Unreachable (.Ok ()) emitted).1
    have observation := compiler_observe_frame_raw ops {middle with reachable := false} state status after observed
    unfold UnreachableFrame
    rw [observation, emission]

theorem UnreachableEffect.capacity {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : UnreachableEffect ops before state status after) (law : Platform.AllocCorrect ops) :
    before.function.slot_count.val ≤ after.function.slot_count.val := by
  cases effect with
  | dead dead observed =>
    have post := compiler_observe_inv ops law before state
    rw [observed, WP.spec_ok] at post
    exact post.2
  | rejected live emitted =>
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after .Unreachable _ emitted).1
    rw [frame]
  | @emitted middle _ _ live emitted observed =>
    have post := compiler_observe_inv ops law {middle with reachable := false} state
    rw [observed, WP.spec_ok] at post
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before middle .Unreachable (.Ok ()) emitted).1
    change middle = _ at frame
    have same := congrArg (fun c : runtime.compiler.FunctionCompiler A => c.function.slot_count) frame
    change middle.function.slot_count = before.function.slot_count at same
    have bound := post.2
    change middle.function.slot_count.val ≤ after.function.slot_count.val at bound
    rw [same] at bound
    exact bound

theorem UnreachableEffect.code {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : UnreachableEffect ops before state status after) (law : Platform.AllocCorrect ops) :
    after.function.code.val = before.function.code.val ∨
      after.function.code.val = before.function.code.val ++ [.Unreachable] := by
  cases effect with
  | dead dead observed =>
    have frame := compiler_observe_frame_raw ops before state status after observed
    exact Or.inl (by rw [frame])
  | rejected live emitted =>
    exact ((runtime.compiler.FunctionCompiler.emit.inv ops before after .Unreachable _ emitted).2 law).1
  | @emitted middle _ _ live emitted observed =>
    have frame := compiler_observe_frame_raw ops {middle with reachable := false} state status after observed
    have code := ((runtime.compiler.FunctionCompiler.emit.inv ops before middle .Unreachable (.Ok ()) emitted).2 law).1
    have same := congrArg (fun c : runtime.compiler.FunctionCompiler A => c.function.code) frame
    change after.function.code = middle.function.code at same
    rw [same]
    exact code

/-- Emission bounds suffice for normal return; no input stack layout is needed. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.total
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  split
  · step with runtime.compiler.FunctionCompiler.emit.total ops law before .Unreachable codeFits sourceFits coordinateFits
      as ⟨reply, middle, total⟩
    cases reply with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact WP.spec_mono (compiler_observe ops law {middle with reachable := false} state) (fun _ _ => True.intro)
  · exact WP.spec_mono (compiler_observe ops law before state) (fun _ _ => True.intro)

/-- Available execution consumes one instruction on live input and none on dead input. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.available
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat)
    (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand before state bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
        used.val = before.budget.instructions.val + (if before.reachable then 1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  by_cases live : before.reachable = true
  · rw [if_pos live]
    step with runtime.compiler.FunctionCompiler.emit.available ops bound available before .Unreachable
      demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
      demand.coordinate demand.instruction as ⟨reply, middle, accepted, emitted⟩
    obtain ⟨used, code, sources, frame, usedEq, _, _⟩ := emitted
    rw [accepted]
    subst middle
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available
      {before with
        reachable := false
        budget := {before.budget with instructions := used}
        function := {before.function with code, source_offsets := sources}}
      state demand.operands demand.slots)
    intro output post
    exact ⟨post.1, used, post.2, by simpa only [live, ite_true] using usedEq⟩
  · rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available before state demand.operands demand.slots)
    intro output post
    exact ⟨post.1, before.budget.instructions, by simpa only using post.2, by simp only [if_neg live, Nat.add_zero]⟩

end Itasca.Compiler

end

/-! ## ReturnContracts -/

section

/-! Canonical return-callback contracts retain the selected root frame, checked
result source, emission and final observation, including partial failures. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

inductive ReturnEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | dead {status after} (dead : before.reachable = false)
      (observed : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
      ReturnEffect ops before state status after
  | underflow {frame} (live : before.reachable = true)
      (selected : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) before.frames 0#usize = .ok frame)
      (source : lift (U32.checked_sub before.height frame.results) = .ok none) :
      ReturnEffect ops before state (.Err .OutOfMemory) before
  | rejected {frame source error after} (live : before.reachable = true)
      (selected : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) before.frames 0#usize = .ok frame)
      (position : lift (U32.checked_sub before.height frame.results) = .ok (some source))
      (emitted : runtime.compiler.FunctionCompiler.emit ops before (.Return source frame.results) = .ok (.Err error, after)) :
      ReturnEffect ops before state (.Err error) after
  | emitted {frame source middle status after} (live : before.reachable = true)
      (selected : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) before.frames 0#usize = .ok frame)
      (position : lift (U32.checked_sub before.height frame.results) = .ok (some source))
      (emitted : runtime.compiler.FunctionCompiler.emit ops before (.Return source frame.results) = .ok (.Ok (), middle))
      (observed : runtime.compiler.FunctionCompiler.observe ops {middle with reachable := false} state = .ok (status, after)) :
      ReturnEffect ops before state status after

/-- Dead input bypasses emission entirely. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.dead
    {A : Type} (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : before.reachable = false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state =
      runtime.compiler.FunctionCompiler.observe ops before state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return,
    dead, Bool.false_eq_true, ite_false]

/-- Normal returns retain their actual emission and observation evidence. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv
    {A : Type} (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (status, after)) :
    ReturnEffect ops before state status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at called
  cases live : before.reachable with
  | false =>
    simp only [live, Bool.false_eq_true, ite_false] at called
    exact .dead live called
  | true =>
    simp only [live, ite_true] at called
    obtain ⟨frame, selected, rest⟩ := bind_ok_inv _ _ _ called
    obtain ⟨source, position, rest⟩ := bind_ok_inv _ _ _ rest
    cases source with
    | none =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      exact .underflow live selected position
    | some source =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨reply, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error =>
        simp only [uncurry_apply_pair,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        exact .rejected live selected position emitted
      | Ok value =>
        cases value
        simp only [uncurry_apply_pair, bind_ok] at rest
        exact .emitted live selected position emitted rest

/-- Successful returns observe a compiler whose reachability is false. -/
theorem ReturnEffect.observation {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    (effect : ReturnEffect ops before state (.Ok ()) after) :
    ∃ middle, middle.reachable = false ∧
      runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  cases effect with
  | dead dead observed => exact ⟨_, dead, observed⟩
  | emitted live selected position emitted observed => exact ⟨_, rfl, observed⟩

/-- Fields permitted to change on a normal return-callback return. -/
def ReturnFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget
    before := after.before
    height := after.height
    next_source := after.next_source
    reachable := after.reachable
    function := {before.function with
      code := after.function.code
      source_offsets := after.function.source_offsets
      max_stack := after.function.max_stack
      slot_count := after.function.slot_count}}

theorem ReturnEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ReturnEffect ops before state status after) : ReturnFrame before after := by
  cases effect with
  | dead dead observed =>
    have frame := compiler_observe_frame_raw ops before state status after observed
    unfold ReturnFrame
    rw [frame]
  | underflow live selected position => rfl
  | rejected live selected position emitted =>
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after _ _ emitted).1
    unfold ReturnFrame
    rw [frame]
  | @emitted frame source middle _ _ live selected position emitted observed =>
    have emission := (runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).1
    have observation := compiler_observe_frame_raw ops {middle with reachable := false} state status after observed
    unfold ReturnFrame
    rw [observation, emission]

theorem ReturnEffect.capacity {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ReturnEffect ops before state status after) (law : Platform.AllocCorrect ops) :
    before.function.slot_count.val ≤ after.function.slot_count.val := by
  cases effect with
  | dead dead observed =>
    have post := compiler_observe_inv ops law before state
    rw [observed, WP.spec_ok] at post
    exact post.2
  | underflow live selected position => exact Nat.le_refl _
  | rejected live selected position emitted =>
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after _ _ emitted).1
    rw [frame]
  | @emitted frame source middle _ _ live selected position emitted observed =>
    have post := compiler_observe_inv ops law {middle with reachable := false} state
    rw [observed, WP.spec_ok] at post
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).1
    change middle = _ at frame
    have same := congrArg (fun c : runtime.compiler.FunctionCompiler A => c.function.slot_count) frame
    change middle.function.slot_count = before.function.slot_count at same
    have bound := post.2
    change middle.function.slot_count.val ≤ after.function.slot_count.val at bound
    rw [same] at bound
    exact bound

/-- A live return needs a root frame; checked source underflow is a normal error. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.total
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (root : before.reachable = true → 0 < before.frames.val.length)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  by_cases live : before.reachable = true
  · rw [if_pos live]
    have framesBound := root live
    step as ⟨frame, selected⟩
    step as ⟨source, position⟩
    cases source with
    | none => simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | some source =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with runtime.compiler.FunctionCompiler.emit.total ops law before (.Return source frame.results) codeFits sourceFits coordinateFits
        as ⟨reply, middle⟩
      cases reply with
      | Err error =>
        simp only [bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      | Ok value =>
        cases value
        simp only [bind_ok]
        exact WP.spec_mono (compiler_observe ops law {middle with reachable := false} state) (fun _ _ => True.intro)
  · rw [if_neg live]
    exact WP.spec_mono (compiler_observe ops law before state) (fun _ _ => True.intro)

/-- Successful return charges one instruction on live input and none on dead input. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.available
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat)
    (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand before state bound) (body : runtime.compiler.Frame)
    (bodyFrame : before.reachable = true → before.frames.val[0]? = some body)
    (height : before.reachable = true → body.results.val ≤ before.height.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
        used.val = before.budget.instructions.val + (if before.reachable then 1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  by_cases live : before.reachable = true
  · rw [if_pos live]
    have framesBound : 0 < before.frames.length := (List.getElem?_eq_some_iff.mp (bodyFrame live)).1
    step as ⟨frame, selected⟩
    have same : frame = body := selected.trans (List.getElem?_eq_some_iff.mp (bodyFrame live)).2
    rw [same]
    have resultFits := height live
    step as ⟨source, position⟩
    cases source with
    | none => simp only at position; omega
    | some source =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with runtime.compiler.FunctionCompiler.emit.available ops bound available before (.Return source body.results)
        demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
        demand.coordinate demand.instruction as ⟨reply, middle, accepted, emitted⟩
      obtain ⟨used, code, sources, frame, usedEq, _, _⟩ := emitted
      rw [accepted]
      subst middle
      simp only [bind_ok]
      apply WP.spec_mono (compiler_observe_available_budget ops bound available
        {before with
          reachable := false
          budget := {before.budget with instructions := used}
          function := {before.function with code, source_offsets := sources}}
        state demand.operands demand.slots)
      intro output post
      exact ⟨post.1, used, post.2, by simpa only [live, ite_true] using usedEq⟩
  · rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available before state demand.operands demand.slots)
    intro output post
    exact ⟨post.1, before.budget.instructions, by simpa only using post.2, by simp only [if_neg live, Nat.add_zero]⟩

end Itasca.Compiler

end

end

/-! ## TableBranchContracts -/

section

/-! Canonical contracts for publishing table targets and lowering the target loop.
Operational traces retain intermediate states without allocator assumptions. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

/-- One target records its current PC, publishes that PC in the side table,
then lowers the selected branch. Ordinary errors retain their actual state. -/
def TableBranchEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ answer current, runtime.compiler.FunctionCompiler.pc ops before = .ok (answer, current) ∧
    match answer with
    | .Err error => status = .Err error ∧ after = current
    | .Ok target => ∃ pushed budget table,
      runtime.compiler.Budget.push ops current.budget current.function.jump_tables target = .ok (pushed, budget, table) ∧
      let staged := {current with budget, function := {current.function with jump_tables := table}}
      match pushed with
      | .Err error => status = .Err error ∧ after = staged
      | .Ok _ => ∃ depth,
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) current.table_depths index = .ok depth ∧
        runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (status, after)

/-- Inversion records all three stages, including ordinary-error exits. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.table_branch.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (status, after)) :
    TableBranchEffect ops before after index status := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at called
  obtain ⟨⟨answer, current⟩, pc, rest⟩ := bind_ok_inv _ _ _ called
  refine ⟨answer, current, pc, ?_⟩
  cases answer with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact ⟨rest.1.symm, rest.2.symm⟩
  | Ok target =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨answer, budget, table⟩, pushed, rest⟩ := bind_ok_inv _ _ _ rest
    refine ⟨answer, budget, table, pushed, ?_⟩
    cases answer with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      exact ⟨rest.1.symm, rest.2.symm⟩
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨depth, selected, branch⟩ := bind_ok_inv _ _ _ rest
      exact ⟨depth, selected, branch⟩

/-- Normality composes representable table publication with the branch's
normality certificate for every allocation-accounting outcome. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.table_branch.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (tableFits : before.function.jump_tables.val.length < Usize.max)
    (branchReady : ∀ budget table, runtime.compiler.control.FunctionCompiler.branch ops
      {before with budget, function := {before.function with jump_tables := table}}
      depth 1#u32 false ⦃ _ => True ⦄) :
    runtime.compiler.control.FunctionCompiler.table_branch ops before index ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch
  step with compiler_pc ops before as ⟨answer, current, _, _, budget, same⟩
  subst current
  cases answer with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok target =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law budget before.function.jump_tables target tableFits as
      ⟨answer, budget, table, _⟩
    cases answer with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have inside := (List.getElem?_eq_some_iff.mp lookup).1
      step as ⟨actual, found⟩
      have same : actual = depth := found.trans (List.getElem?_eq_some_iff.mp lookup).2
      subst actual
      rw [(List.getElem?_eq_some_iff.mp lookup).2]
      exact branchReady budget table

/-- Available publication leaves the instruction budget untouched before the
branch; the child certificate describes its exact successful result. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.table_branch.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (pcFits : before.function.code.val.length ≤ U32.max)
    (tableFits : before.function.jump_tables.length < Usize.max)
    (tableReserve : before.function.jump_tables.length + 1 ≤ bound)
    (post : runtime.compiler.FunctionCompiler A → Prop)
    (branchReady : ∀ table, runtime.compiler.control.FunctionCompiler.branch ops
      {before with function := {before.function with jump_tables := table}}
      depth 1#u32 false ⦃ (status, after) => status = .Ok () ∧ post after ⦄) :
    runtime.compiler.control.FunctionCompiler.table_branch ops before index
      ⦃ (status, after) => status = .Ok () ∧ post after ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch
  step with compiler_pc_available ops before pcFits as ⟨answer, current, same, target, accepted, _⟩
  subst current
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with budget_push_available ops bound available before.budget before.function.jump_tables target
    tableFits tableReserve as ⟨answer, budget, table, accepted, same, _⟩
  subst answer budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual, found⟩
  have same : actual = depth := found.trans (List.getElem?_eq_some_iff.mp lookup).2
  subst actual
  rw [(List.getElem?_eq_some_iff.mp lookup).2]
  exact branchReady table

/-- The final Rust status in an extracted compiler snapshot. -/
def snapshotStatus {A : Type} (output : CompilerSnapshot A) :
    core.result.Result Unit Itasca.error.VisitError :=
  let (_, _, _, _, _, _, _, _, _, _, _, _, result) := output
  result

/-- A finite table-target traversal, retaining failures as well as success. -/
inductive TableLoopEffect {A : Type} (ops : runtime.platform.Alloc A) :
    runtime.compiler.FunctionCompiler A → Nat → core.result.Result Unit Itasca.error.VisitError →
      CompilerSnapshot A → Prop where
  | done (before) (index) (status)
      (finished : before.table_depths.val.length ≤ index ∨ status ≠ .Ok ()) :
      TableLoopEffect ops before index status (compilerSnapshot before status)
  | step {before middle output result} (index : Usize)
      (inside : index.val < before.table_depths.val.length)
      (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (result, middle))
      (rest : TableLoopEffect ops middle (index.val + 1) result output) :
      TableLoopEffect ops before index.val (.Ok ()) output

/-- Loop inversion retains each published target and the actual stopping state. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops before index status = .ok output) :
    TableLoopEffect ops before index.val status output := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop at called
    rw [loop] at called
    simp only [runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body, bind_ok] at called
    split at called
    next inside =>
      have indexBound : index.val < before.table_depths.val.length := by scalar_tac
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false, Result.ok.injEq] at called
        subst output
        exact .done before index.val (.Err error) (Or.inr (by intro impossible; cases impossible))
      | Ok value =>
        cases value
        simp only [core.result.Result.is_ok, bind_ok, ite_true, Std.bind_assoc] at called
        obtain ⟨⟨result, middle⟩, branch, tail⟩ := bind_ok_inv _ _ _ called
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by
          simpa only [UScalar.ofNatCore_val_eq] using arithmetic.2.1
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have continued : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
            ops middle nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body,
            core.result.Result.is_ok] using tail
        exact .step index indexBound branch (by
          simpa only [progress] using ih _ smaller middle nextIndex result continued rfl)
    next outside =>
      simp only [bind_ok, Result.ok.injEq] at called
      subst output
      exact .done before index.val status (Or.inl (by scalar_tac))

/-- Dispatch lowering retains bounded side-table coordinates, selector decoding,
emission, and the actual target-loop call, including each ordinary error exit. -/
def LowerTableEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ startResult, runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.jump_tables) = .ok startResult ∧
    match startResult with
    | .Err error => status = .Err error ∧ after = before
    | .Ok start => ∃ lengthResult,
      runtime.compiler.bounded_index (alloc.vec.Vec.len before.table_depths) = .ok lengthResult ∧
      match lengthResult with
      | .Err error => status = .Err error ∧ after = before
      | .Ok length => ∃ operand,
        runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok operand ∧
        match operand with
        | .Err error => status = .Err error ∧ after = before
        | .Ok selector => ∃ emitted middle,
          runtime.compiler.FunctionCompiler.emit ops before (.JumpTable selector start length) = .ok (emitted, middle) ∧
          match emitted with
          | .Err error => status = .Err error ∧ after = middle
          | .Ok _ => ∃ output,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops middle 0#usize (.Ok ()) = .ok output ∧
            status = snapshotStatus output ∧ after = snapshotCompiler output

/-- One inversion exposes dispatch construction and all target-loop evidence. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (status, after)) :
    LowerTableEffect ops before after status := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches at called
  obtain ⟨startResult, startCall, rest⟩ := bind_ok_inv _ _ _ called
  refine ⟨startResult, startCall, ?_⟩
  cases startResult with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact ⟨rest.1.symm, rest.2.symm⟩
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨lengthResult, lengthCall, rest⟩ := bind_ok_inv _ _ _ rest
    refine ⟨lengthResult, lengthCall, ?_⟩
    cases lengthResult with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      exact ⟨rest.1.symm, rest.2.symm⟩
    | Ok length =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨operand, operandCall, rest⟩ := bind_ok_inv _ _ _ rest
      refine ⟨operand, operandCall, ?_⟩
      cases operand with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        exact ⟨rest.1.symm, rest.2.symm⟩
      | Ok selector =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨emitted, middle⟩, emitCall, rest⟩ := bind_ok_inv _ _ _ rest
        refine ⟨emitted, middle, emitCall, ?_⟩
        cases emitted with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          exact ⟨rest.1.symm, rest.2.symm⟩
        | Ok value =>
          cases value
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨output, loopCall, rest⟩ := bind_ok_inv _ _ _ rest
          refine ⟨output, loopCall, ?_⟩
          rcases output with ⟨signatures, functionSlots, budget, batchStart, function, frames,
            reachable, nextSource, operands, height, offsets, depths, result⟩
          simp only [uncurry_apply_pair, bind_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          exact ⟨rest.1.symm, rest.2.symm⟩

/-- Dispatch normality composes emission with a certified target-loop continuation. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (loopReady : ∀ start length selector middle,
      EmittedExact before middle (.JumpTable selector start length) →
      runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops middle 0#usize (.Ok ()) ⦃ _ => True ⦄) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops before ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches
  step as ⟨startResult, _⟩
  cases startResult with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨lengthResult, _⟩
    cases lengthResult with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok length =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with compiler_operand_total ops before 1#usize as ⟨operand, _⟩
      cases operand with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok selector =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨⟨status, middle⟩, emitted, _⟩ := WP.spec_imp_exists
          (runtime.compiler.FunctionCompiler.emit.total ops law before (.JumpTable selector start length)
            codeFits sourceFits coordinate)
        rw [emitted, bind_ok]
        simp only [uncurry_apply_pair]
        cases status with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, WP.spec_ok]
        | Ok value =>
          cases value
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          have effect := ((runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).2 law).2 rfl
          step with loopReady start length selector middle effect

/-- Independent room for dispatch publication and bounded table coordinates. -/
structure LowerTableDemand {A : Type} (before : runtime.compiler.FunctionCompiler A) (bound : Nat)
    : Prop extends CopyDemand before bound where
  tableStart : before.function.jump_tables.length ≤ U32.max
  depthCount : before.table_depths.length ≤ U32.max

/-- Available dispatch construction delegates the remaining target publication
to a success certificate at the exact emitted intermediate state. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (selector : U32)
    (selectorReady : runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok selector))
    (demand : LowerTableDemand before bound)
    (post : runtime.compiler.FunctionCompiler A → Prop)
    (loopReady : ∀ start length middle,
      EmittedExact before middle (.JumpTable selector start length) →
      runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops middle 0#usize (.Ok ())
        ⦃ output => snapshotStatus output = .Ok () ∧ post (snapshotCompiler output) ⦄) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops before
      ⦃ (status, after) => status = .Ok () ∧ post after ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches
  step with bounded_index_available (alloc.vec.Vec.len before.function.jump_tables) demand.tableStart
    as ⟨answer, start, accepted, _⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with bounded_index_available (alloc.vec.Vec.len before.table_depths) demand.depthCount
    as ⟨answer, length, accepted, _⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, selectorReady]
  step with runtime.compiler.FunctionCompiler.emit.available ops bound available before (.JumpTable selector start length)
    demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
    demand.coordinate demand.instruction as ⟨answer, middle, accepted, emitted⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with loopReady start length middle emitted as
    ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
      nextSource, operands, height, offsets, depths, result, accepted, effect⟩
  exact ⟨accepted, effect⟩

/-- A single target-loop induction composes a caller's preserved invariant and
terminal postcondition. The index strictly advances regardless of branch status. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.spec {A : Type}
    (ops : runtime.platform.Alloc A)
    (invariant : runtime.compiler.FunctionCompiler A → Nat → core.result.Result Unit Itasca.error.VisitError → Prop)
    (post : CompilerSnapshot A → Prop)
    (advance : ∀ current (index : Usize), invariant current index.val (.Ok ()) →
      index.val < current.table_depths.val.length →
      runtime.compiler.control.FunctionCompiler.table_branch ops current index
        ⦃ (status, after) => invariant after (index.val + 1) status ⦄)
    (finish : ∀ current index status, invariant current index status →
      (current.table_depths.val.length ≤ index ∨ status ≠ .Ok ()) →
      post (compilerSnapshot current status))
    (before : runtime.compiler.FunctionCompiler A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (held : invariant before index.val status) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops before index status ⦃ post ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
  apply loop.spec_decr_nat (fun p => Usize.max - p.2.1.val)
    (fun p => invariant p.1 p.2.1.val p.2.2)
  · rintro ⟨current, i, result⟩ currentHeld
    dsimp only at currentHeld
    unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body
    simp only
    split
    next more =>
      have inside : i.val < current.table_depths.val.length := by scalar_tac
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false, WP.spec_ok]
        exact finish current i.val (.Err error) currentHeld (Or.inr (by intro impossible; cases impossible))
      | Ok value =>
        cases value
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with advance current i currentHeld inside as ⟨result, next, nextHeld⟩
        step as ⟨nextIndex, increment⟩
        refine ⟨?_, by scalar_tac⟩
        have progress : nextIndex.val = i.val + 1 := by scalar_tac
        simpa only [progress] using nextHeld
    next done =>
      simp only [WP.spec_ok]
      exact finish current i.val result currentHeld (Or.inl (by scalar_tac))
  · exact held

/-- Table lowering changes only allocation accounting, branch publication, and
its side-table vector; all reader and source coordinates remain fixed. -/
def TableFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget
    frames := after.frames
    function := {before.function with
      code := after.function.code
      source_offsets := after.function.source_offsets
      jump_tables := after.function.jump_tables}}

theorem TableFrame.refl {A : Type} (before : runtime.compiler.FunctionCompiler A) : TableFrame before before := rfl

theorem TableFrame.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : TableFrame before middle) (second : TableFrame middle after) : TableFrame before after := by
  unfold TableFrame at *
  rw [second, first]

theorem TableBranchEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index status}
    (effect : TableBranchEffect ops before after index status) : TableFrame before after := by
  obtain ⟨answer, current, called, rest⟩ := effect
  have pc := compiler_pc ops before
  rw [called, WP.spec_ok] at pc
  obtain ⟨budget, same⟩ := pc.2.2
  change current = {before with budget} at same
  subst current
  cases answer with
  | Err error =>
    obtain ⟨_, same⟩ := rest
    subst after
    rfl
  | Ok target =>
    obtain ⟨answer, budget, table, _, rest⟩ := rest
    cases answer with
    | Err error =>
      obtain ⟨_, same⟩ := rest
      subst after
      rfl
    | Ok value =>
      cases value
      obtain ⟨depth, _, called⟩ := rest
      have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops _ after depth 1#u32 false status called).frame
      unfold TableFrame
      rw [frame]

theorem TableLoopEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before index status output} (effect : TableLoopEffect (A := A) ops before index status output) :
    TableFrame before (snapshotCompiler output) := by
  induction effect with
  | done before index status finished => exact TableFrame.refl before
  | step index inside called rest ih =>
    exact (runtime.compiler.control.FunctionCompiler.table_branch.inv ops _ _ index _ called).frame.trans ih

/-- Successful target publication retains the actual branch call and exact
side-table append, sufficient for all existing target-layout certificates. -/
theorem TableBranchEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index : Usize}
    (effect : TableBranchEffect ops before after index (.Ok ()))
    (law : Platform.AllocCorrect ops) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth) :
    ∃ target budget table,
      target.val = before.function.code.val.length ∧
      table.val = before.function.jump_tables.val ++ [target] ∧
      runtime.compiler.control.FunctionCompiler.branch ops
        {before with budget, function := {before.function with jump_tables := table}}
        depth 1#u32 false = .ok (.Ok (), after) := by
  obtain ⟨answer, current, called, rest⟩ := effect
  have pc := compiler_pc ops before
  rw [called, WP.spec_ok] at pc
  obtain ⟨_, coordinate, budget, same⟩ := pc
  change current = {before with budget} at same
  subst current
  cases answer with
  | Err error => cases rest.1
  | Ok target =>
    have targetEq := coordinate target rfl
    obtain ⟨answer, finalBudget, table, pushed, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      obtain ⟨found, read, called⟩ := rest
      have inside := (List.getElem?_eq_some_iff.mp lookup).1
      have readSpec : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
          before.table_depths index ⦃ out => out = depth ⦄ := by
        step as ⟨out, exactValue⟩
        exact exactValue.trans (List.getElem?_eq_some_iff.mp lookup).2
      rw [read, WP.spec_ok] at readSpec
      subst found
      have tableEq := (budget_push_success ops law budget finalBudget before.function.jump_tables table target pushed).2
      exact ⟨target, finalBudget, table, targetEq, tableEq, called⟩

theorem EmitFrame.table {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (effect : EmitFrame before after) : TableFrame before after := by
  unfold TableFrame
  rw [effect]

theorem LowerTableEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {status}
    (effect : LowerTableEffect ops before after status) : TableFrame before after := by
  obtain ⟨start, _, rest⟩ := effect
  cases start with
  | Err error => exact rest.2 ▸ TableFrame.refl before
  | Ok start =>
    obtain ⟨length, _, rest⟩ := rest
    cases length with
    | Err error => exact rest.2 ▸ TableFrame.refl before
    | Ok length =>
      obtain ⟨operand, _, rest⟩ := rest
      cases operand with
      | Err error => exact rest.2 ▸ TableFrame.refl before
      | Ok selector =>
        obtain ⟨answer, middle, emitted, rest⟩ := rest
        have first := (runtime.compiler.FunctionCompiler.emit.inv ops before middle _ answer emitted).1.table
        cases answer with
        | Err error => exact rest.2 ▸ first
        | Ok value =>
          cases value
          obtain ⟨output, called, _, same⟩ := rest
          rw [same]
          exact first.trans (runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.inv ops middle 0#usize (.Ok ()) output called).frame

/-- Successful dispatch exposes exact coordinates, selector, emission and loop. -/
theorem LowerTableEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A}
    (effect : LowerTableEffect ops before after (.Ok ())) (law : Platform.AllocCorrect ops) :
    ∃ start length selector middle output,
      start.val = before.function.jump_tables.val.length ∧
      length.val = before.table_depths.val.length ∧
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok selector) ∧
      EmittedExact before middle (.JumpTable selector start length) ∧
      runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops middle 0#usize (.Ok ()) = .ok output ∧
      snapshotStatus output = .Ok () ∧ snapshotCompiler output = after := by
  obtain ⟨start, startCall, rest⟩ := effect
  cases start with
  | Err error => cases rest.1
  | Ok start =>
    have startSpec := bounded_index (alloc.vec.Vec.len before.function.jump_tables)
    rw [startCall, WP.spec_ok] at startSpec
    have startEq := startSpec start rfl
    obtain ⟨length, lengthCall, rest⟩ := rest
    cases length with
    | Err error => cases rest.1
    | Ok length =>
      have lengthSpec := bounded_index (alloc.vec.Vec.len before.table_depths)
      rw [lengthCall, WP.spec_ok] at lengthSpec
      have lengthEq := lengthSpec length rfl
      obtain ⟨operand, operandCall, rest⟩ := rest
      cases operand with
      | Err error => cases rest.1
      | Ok selector =>
        obtain ⟨answer, middle, emitted, rest⟩ := rest
        cases answer with
        | Err error => cases rest.1
        | Ok value =>
          cases value
          obtain ⟨output, called, successful, same⟩ := rest
          exact ⟨start, length, selector, middle, output, startEq, lengthEq, operandCall,
            ((runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).2 law).2 rfl,
            called, successful.symm, same.symm⟩

end Itasca.Compiler

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

/-- One successful table target records its current code PC before lowering
that target's branch. The only intermediate changes are allocation accounting
and the exact append to the retained jump table. -/
theorem compiler_table_branch_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ∃ target budget table,
      target.val = before.function.code.val.length ∧
      table.val = before.function.jump_tables.val ++ [target] ∧
      runtime.compiler.control.FunctionCompiler.branch ops
        { before with budget, function := { before.function with jump_tables := table } }
        depth 1#u32 false = .ok (.Ok (),after) := by
  exact (runtime.compiler.control.FunctionCompiler.table_branch.inv ops before after index (.Ok ()) accepted).success law depth lookup

end Itasca.Compiler

end
