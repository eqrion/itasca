import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap

/-!
Sections, each formerly its own module: BranchSuccessForward, BranchSuccessLoop, BranchSuccessConditional.
-/

/-! ## BranchSuccessForward -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem branch_transfer_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false = .ok (.Ok (), after)) :
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
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 0#u32 false (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (0#u32) ready law
  simp only [branchOutput, width, if_neg nonelided, branchTarget, loop, branchJump,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_neg nonelided, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at updated
  obtain ⟨fixups, frames, appended⟩ := updated
  exact ⟨code, fixups, site, sitePosition, frames, appended⟩

theorem branch_elided_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false = .ok (.Ok (), after)) :
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
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 0#u32 false (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (0#u32) ready law
  simp only [branchOutput, width, if_pos elided, branchTarget, loop, branchJump,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_pos elided, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at updated
  obtain ⟨fixups, frames, appended⟩ := updated
  exact ⟨code, fixups, site, sitePosition, frames, appended⟩

end Itasca.Runtime.Compiler

end

/-! ## BranchSuccessLoop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem branch_transfer_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false = .ok (.Ok (), after)) :
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
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 0#u32 false (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (0#u32) ready law
  simp only [branchOutput, width, if_neg nonelided, branchTarget, loop, branchJump,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_neg nonelided, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at updated
  exact ⟨code, updated⟩

theorem branch_elided_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false = .ok (.Ok (), after)) :
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
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 0#u32 false (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (0#u32) ready law
  simp only [branchOutput, width, if_pos elided, branchTarget, loop, branchJump,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_pos elided, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at updated
  exact ⟨code, updated⟩

end Itasca.Runtime.Compiler

end

/-! ## BranchSuccessConditional -/

section

/-!
Successful conditional branches for loops and forward transfers. Keeps the target distinction visible while joining their common callback result.
-/

/-! ## Branch Success Conditional -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem branch_if_elided_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.JumpIfNonZero condition core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length ∧
          after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] := by
  have width : branchWidth frame = frame.results := by
    cases kind : frame.kind <;> simp only [branchWidth, kind]
    exact False.elim (forward kind)
  have loop : branchLoop frame.kind = false := by
    cases kind : frame.kind <;> simp only [branchLoop]
    exact False.elim (forward kind)
  have ready : true = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (condition)) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact same ▸ called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 1#u32 true (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (condition) ready law
  simp only [branchOutput, width, if_pos elided, branchTarget, loop, branchJump,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_pos elided, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at updated
  obtain ⟨fixups, frames, appended⟩ := updated
  exact ⟨code, fixups, site, sitePosition, frames, appended⟩

end Itasca.Runtime.Compiler

end

/-! ## Branch Success Conditional Transfer -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem branch_if_transfer_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length + 3)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.JumpIfZero condition resume, transferInstruction frame.height source frame.results, .Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length + 2 ∧
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
  have ready : true = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (condition)) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact same ▸ called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 1#u32 true (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (condition) ready law
  have actualPosition := resumeValid rfl (by simpa only [width] using nonelided)
  have sameResume : actualResume = resume := by
    apply UScalar.eq_of_val_eq
    omega
  subst actualResume
  simp only [branchOutput, width, if_neg nonelided, branchTarget, loop, branchJump,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_neg nonelided, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at updated
  obtain ⟨fixups, frames, appended⟩ := updated
  exact ⟨code, fixups, site, sitePosition, frames, appended⟩

end Itasca.Runtime.Compiler

end

/-! ## Branch Success Conditional Loop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem branch_if_elided_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.JumpIfNonZero condition frame.start_pc] ∧
        after.frames = compiler.frames := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kindEq]
  have loop : branchLoop frame.kind = true := by
    simp only [branchLoop, kindEq]
  have ready : true = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (condition)) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact same ▸ called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 1#u32 true (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (condition) ready law
  simp only [branchOutput, width, if_pos elided, branchTarget, loop, branchJump,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_pos elided, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at updated
  exact ⟨code, updated⟩

theorem branch_if_transfer_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length + 3)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.JumpIfZero condition resume, transferInstruction frame.height source frame.params, .Jump frame.start_pc] ∧
        after.frames = compiler.frames := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kindEq]
  have loop : branchLoop frame.kind = true := by
    simp only [branchLoop, kindEq]
  have nonelided : ¬ (frame.params = 0#u32 ∨ source = frame.height) :=
    fun choice => choice.elim nonempty different
  have ready : true = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (condition)) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact same ▸ called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 1#u32 true (.Ok ()) accepted
  obtain ⟨actualResume, site, code, sitePosition, updated, resumeValid⟩ :=
    effect.success ⟨index, frame, lookup, position⟩ source
      (by simpa only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] using sourcePosition)
      (condition) ready law
  have actualPosition := resumeValid rfl (by simpa only [width] using nonelided)
  have sameResume : actualResume = resume := by
    apply UScalar.eq_of_val_eq
    omega
  subst actualResume
  simp only [branchOutput, width, if_neg nonelided, branchTarget, loop, branchJump,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at code
  simp only [branchInstructionCount, width, if_neg nonelided, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, Nat.add_zero] at sitePosition
  simp only [BranchFrameUpdate, loop, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at updated
  exact ⟨code, updated⟩

end Itasca.Runtime.Compiler

end

end
