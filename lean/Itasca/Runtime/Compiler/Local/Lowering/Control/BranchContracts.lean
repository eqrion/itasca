import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Relations.Control

/-! Canonical branch contracts retain the selected operand interval and the
ordered helper calls, including partial progress before ordinary errors.

Main declarations: `branch.inv`, `branch.total`, and `branch.available`. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

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

end Itasca.Runtime.Compiler
