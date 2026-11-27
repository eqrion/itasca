import Itasca.Runtime.Compiler.Local.Relations.Function.EnvironmentContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSuccess
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectAndStatefulCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ClosingContracts
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessConditional

/-!
Proofs for Runtime / Compiler / Local / Relations / Table.

This module collects SignaturesAndAuxiliaryTables, ControlTablePreservation.
Each section documents its contracts and consumers.
-/

/-! ## SignaturesAndAuxiliaryTables -/

section

/-!
# Signatures And Auxiliary Tables

Signature lookups and stateful auxiliary tables retain the mappings required by compiler callbacks.
-/

/-! ## SignatureTable -/

section

/-! The actual scheduler loop constructs a source-aligned signature table
from every module type, retaining exact value and word arities. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem SignatureSequence.lookup {signatures types}
    (sequence : SignatureSequence signatures types) {index : Nat} {signature : runtime.compiler.Signature}
    (found : signatures[index]? = some signature) :
    ∃ ty : Itasca.wasm_types.FuncType, types[index]? = some ty ∧ SignatureMatches signature
      (ty.params.val.map Itasca.Translation.valueType) (ty.results.val.map Itasca.Translation.valueType) := by
  induction sequence generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst signature
              exact ⟨_, rfl, head⟩
    | succ index => exact ih (by simpa using found)

theorem SignatureSequence.table {signatures : Slice runtime.compiler.Signature}
    {types : List Itasca.wasm_types.FuncType} (sequence : SignatureSequence signatures.val types) :
    SignatureTable signatures (types.map Itasca.Translation.Environment.funcType) := by
  intro index signature found
  obtain ⟨ty, lookup, matched⟩ := SignatureSequence.lookup sequence found
  refine ⟨_, _, ?_, matched⟩
  simp [List.getElem?_map, lookup, Itasca.Translation.Environment.funcType]

@[step] theorem capture_signatures_loop_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.types.val.length)
    (prefixMatches : status = .Ok () → SignatureSequence scheduler.signatures.val (env.types.val.take index.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index status ⦃ out =>
      out.2.2.2.2.2.2.2 = .Ok () → SignatureSequence out.1.val env.types.val ∧
        out.2.1 = scheduler.func_param_slots ∧ out.2.2.2.1 = scheduler.functions ⦄ := by
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.total ops law scheduler env index status bound prefixMatches

end Itasca.Compiler

end

/-! ## StatefulAuxiliaryTables -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096
theorem compiler_stateful_auxiliary_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Stateful.Instruction) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (status, after)) :
    compilerAuxiliaryTables after.function = compilerAuxiliaryTables before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' auxiliary_tables_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    have tables := compiler_observe_tables ops law before after state status accepted
    simpa only [CompilerTables.ofFunction, CompilerTables.mk.injEq, compilerAuxiliaryTables] using
      congrArg (fun t : CompilerTables => (t.simd,t.constants,t.jumpTables)) tables
theorem compiler_indirect_call_auxiliary_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (status, after)) :
    compilerAuxiliaryTables after.function = compilerAuxiliaryTables before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    unfold indirectCallLowering at accepted
    repeat' auxiliary_tables_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    have tables := compiler_observe_tables ops law before after state status accepted
    simpa only [CompilerTables.ofFunction, CompilerTables.mk.injEq, compilerAuxiliaryTables] using
      congrArg (fun t : CompilerTables => (t.simd,t.constants,t.jumpTables)) tables
end Itasca.Compiler

end

end

/-! ## ControlTablePreservation -/

section

open Itasca.Representation

/-! ## BranchTableSkip -/

section

/-!
Skipped forward and loop branches during br_table compilation. The common result preserves the distinct transfer and elided-code cases.
-/

/-! ## Branch Table Skip Forward -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096
theorem branch_transfer_forward_skip_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [transferInstruction frame.height source frame.results, .Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length + 1 ∧
          after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] := by
  have width : branchWidth frame = frame.results := by
    cases kind : frame.kind <;> simp only [branchWidth, kind]
    exact False.elim (forward kind)
  have loop : branchLoop frame.kind = false := by
    cases kind : frame.kind <;> simp only [branchLoop]
    exact False.elim (forward kind)
  have nonelided : ¬ (frame.results = 0#u32 ∨ source = frame.height) :=
    fun choice => choice.elim nonempty different
  have ready : false = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (0#u32)) := by
    intro impossible
    cases impossible
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth skip false (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (0#u32) ready law
  simp only [branchOutput, width, if_neg nonelided, branchTarget, loop, branchJump, Bool.not_false, Bool.and_true, Bool.false_eq_true, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_neg nonelided, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, ite_false, ite_true] at updated
  obtain ⟨fixups, frames, appended⟩ := updated
  exact ⟨code, fixups, site, sitePosition, frames, appended⟩

theorem branch_elided_forward_skip_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length ∧
          after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] := by
  have width : branchWidth frame = frame.results := by
    cases kind : frame.kind <;> simp only [branchWidth, kind]
    exact False.elim (forward kind)
  have loop : branchLoop frame.kind = false := by
    cases kind : frame.kind <;> simp only [branchLoop]
    exact False.elim (forward kind)
  have ready : false = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (0#u32)) := by
    intro impossible
    cases impossible
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth skip false (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (0#u32) ready law
  simp only [branchOutput, width, if_pos elided, branchTarget, loop, branchJump, Bool.not_false, Bool.and_true, Bool.false_eq_true, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_pos elided, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, ite_false, ite_true] at updated
  obtain ⟨fixups, frames, appended⟩ := updated
  exact ⟨code, fixups, site, sitePosition, frames, appended⟩

end Itasca.Compiler

end

/-! ## Branch Table Skip Loop -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096
theorem branch_transfer_loop_skip_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [transferInstruction frame.height source frame.params, .Jump frame.start_pc] ∧
        after.frames = compiler.frames := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kindEq]
  have loop : branchLoop frame.kind = true := by
    simp only [branchLoop, kindEq]
  have nonelided : ¬ (frame.params = 0#u32 ∨ source = frame.height) :=
    fun choice => choice.elim nonempty different
  have ready : false = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (0#u32)) := by
    intro impossible
    cases impossible
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth skip false (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (0#u32) ready law
  simp only [branchOutput, width, if_neg nonelided, branchTarget, loop, branchJump, Bool.not_false, Bool.and_true, Bool.false_eq_true, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_neg nonelided, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, ite_false, ite_true] at updated
  exact ⟨code, updated⟩

theorem branch_elided_loop_skip_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.Jump frame.start_pc] ∧
        after.frames = compiler.frames := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kindEq]
  have loop : branchLoop frame.kind = true := by
    simp only [branchLoop, kindEq]
  have ready : false = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (0#u32)) := by
    intro impossible
    cases impossible
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth skip false (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (0#u32) ready law
  simp only [branchOutput, width, if_pos elided, branchTarget, loop, branchJump, Bool.not_false, Bool.and_true, Bool.false_eq_true, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_pos elided, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, ite_false, ite_true] at updated
  exact ⟨code, updated⟩

end Itasca.Compiler

end

/-! ## Branch Table Skip -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
theorem compiler_branch_forward_skip_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false = .ok (.Ok (), after)) : ∃ fixups,
        after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        BranchHole after.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results ∧
        after.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.results core.num.U32.MAX ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1) ∧
          fixups.val = frame.fixups.val ++ [site] := by
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · have effect := branch_elided_forward_skip_success ops law compiler frame index depth source skip lookup
      position forward elided sourcePosition after accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_pos elided]
      exact ⟨site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩
  · have nonempty : frame.results ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_transfer_forward_skip_success ops law compiler frame index depth source skip lookup
      position forward nonempty different sourcePosition after accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_neg elided]
      exact ⟨by simp [code], site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩

theorem compiler_branch_loop_skip_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.params frame.start_pc ∧
        after.frames = compiler.frames := by
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · have effect := branch_elided_loop_skip_success ops law compiler frame index depth source skip lookup
      position kind elided sourcePosition after accepted
    simpa [branchInstructions, elided] using effect
  · have nonempty : frame.params ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_transfer_loop_skip_success ops law compiler frame index depth source skip lookup
      position kind nonempty different sourcePosition after accepted
    simpa [branchInstructions, elided] using effect
end Itasca.Compiler

end

end

/-! ## BranchTableArguments -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096

def frameBranchWidth (frame : runtime.compiler.Frame) : U32 :=
  match frame.kind with | .Loop => frame.params | _ => frame.results

private theorem vec_read_success {T : Type} (vector : alloc.vec.Vec T) (index : Usize) (value : T)
    (accepted : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) vector index = .ok value) :
    vector.val[index.val]? = some value := by
  change alloc.vec.Vec.index_usize vector index = .ok value at accepted
  unfold alloc.vec.Vec.index_usize at accepted
  split at accepted
  · simp [Result.fail] at accepted
  · rename_i found exact
    cases Result.ok_injective accepted
    exact exact

private theorem checked_add_success (a b out : U32)
    (called : lift (U32.checked_add a b) = .ok (some out)) :
    out.val = a.val + b.val := by
  have spec : lift (U32.checked_add a b)
      ⦃ result => ∀ value, result = some value → value.val = a.val + b.val ⦄ := by
    step as ⟨result,facts⟩
    cases result <;> simp_all
  rw [called,WP.spec_ok] at spec
  exact spec out rfl

private theorem checked_sub_success (a b out : U32)
    (called : lift (U32.checked_sub a b) = .ok (some out)) :
    out.val + b.val = a.val := by
  have spec : lift (U32.checked_sub a b)
      ⦃ result => ∀ value, result = some value → value.val + b.val = a.val ⦄ := by
    step as ⟨result,facts⟩
    cases result <;> simp_all
  rw [called,WP.spec_ok] at spec
  exact spec out rfl

/-- Successful branch lowering itself establishes the selected frame and exact
operand interval; no separate depth or subtraction safety premise is needed. -/
theorem compiler_branch_arguments_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (depth skip : U32)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip false = .ok (.Ok (),after)) :
    ∃ (index : Usize) (frame : runtime.compiler.Frame) (source : U32),
      before.frames.val[index.val]? = some frame ∧
      index.val + depth.val + 1 = before.frames.val.length ∧
      source.val + (frameBranchWidth frame).val + skip.val = before.height.val := by
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip false (.Ok ()) accepted
  obtain ⟨last, converted, index, frame, lastCall, convertedCall, indexCall, frameCall, rest⟩ := effect
  have lookup := vec_read_success before.frames index frame frameCall
  have lastFacts := UScalar.sub_equiv (alloc.vec.Vec.len before.frames) 1#usize
  rw [lastCall] at lastFacts
  have lastSpec : last.val + 1 = before.frames.val.length := by
    have exactValue := lastFacts.2.1
    simpa only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, UScalar.ofNatCore_val_eq] using exactValue.symm
  have convertedEq : converted = UScalar.cast .Usize depth := (Result.ok_injective convertedCall).symm
  have indexFacts := UScalar.sub_equiv last converted
  rw [indexCall] at indexFacts
  have indexSpec : index.val + converted.val = last.val := indexFacts.2.1.symm
  have position : index.val + depth.val + 1 = before.frames.val.length := by
    subst converted
    have castEq : (UScalar.cast .Usize depth).val = depth.val := by scalar_tac
    rw [castEq] at indexSpec
    omega
  obtain ⟨total, totalCall, rest⟩ := rest
  cases total with
  | none => cases rest.1
  | some total =>
    obtain ⟨source, sourceCall, rest⟩ := rest
    cases source with
    | none => cases rest.1
    | some source =>
      have width : branchWidth frame = frameBranchWidth frame := by
        cases frame.kind <;> rfl
      have sum := checked_add_success skip (frameBranchWidth frame) total (by
        simpa only [width] using totalCall)
      have sub := checked_sub_success before.height total source sourceCall
      exact ⟨index, frame, source, lookup, position, by omega⟩
end Itasca.Compiler

end

/-! ## ControlTablePreservation -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096
theorem compiler_enter_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    (CompilerTables.ofFunction after.function) = (CompilerTables.ofFunction before.function) := by
  clear law
  have frame := (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind blockType (.Ok ()) accepted).1
  change after = _ at frame
  rw [frame]
  rfl

theorem compiler_branch_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    (CompilerTables.ofFunction after.function) = (CompilerTables.ofFunction before.function) := by
  have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional (.Ok ()) accepted).frame
  rw [frame]
  rfl

theorem compiler_end_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    (CompilerTables.ofFunction after.function) = (CompilerTables.ofFunction before.function) := by
  have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind blockType (.Ok ()) accepted).frame
  rw [frame]
  rfl

theorem compiler_else_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    (CompilerTables.ofFunction after.function) = (CompilerTables.ofFunction before.function) := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv
    ops before after state blockType (.Ok ()) accepted
  have frame := effect.frame
  change after = _ at frame
  rw [frame]
  rfl

end Itasca.Compiler

end

end
