import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Lowering.Control.ReturnContracts
import Itasca.Runtime.Compiler.Local.Lowering.Control.UnreachableContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels

/-!
Sections, each formerly its own module: LoweringForwardBranch, LoweringLoopBranch, LoweringBranchIf, LoweringConditionalTransfer, LoweringReturn, LoweringTrap.
-/

/-! ## LoweringForwardBranch -/

section

/-! Actual forward BR emission for every non-loop label kind and arbitrary
label depth. Covers all transfer widths and both copy-elision cases, retaining
typed branch holes and exact fixup-list extensions for the closing callback. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096 in
@[step] theorem branch_transfer_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [transferInstruction frame.height source frame.results, .Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length + 1 ∧
          out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
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
  have count : branchInstructionCount false frame source = 2 := by
    simp only [branchInstructionCount, width, if_neg nonelided,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth 0#u32 false
    ({ index := index, frame := frame, lookup := lookup, position := position } : BranchSelection compiler depth)
    (by
      intro actual interval
      have same : actual = source := by
        apply UScalar.eq_of_val_eq
        simp only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] at interval
        omega
      subst actual
      apply Or.inr
      refine ⟨law, ?_⟩
      rw [count]
      refine ⟨?_, ?_, coordinateFits, fun _ => fixupsFit⟩
      · change compiler.function.code.val.length + _ ≤ Usize.max
        omega
      · change compiler.function.source_offsets.val.length + _ ≤ Usize.max
        omega)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  change status = .Ok () at accepted
  rw [accepted] at called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 0#u32 false (.Ok ()) called
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

set_option maxRecDepth 4096 in
@[step] theorem branch_elided_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length ∧
          out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
  have width : branchWidth frame = frame.results := by
    cases kind : frame.kind <;> simp only [branchWidth, kind]
    exact False.elim (forward kind)
  have loop : branchLoop frame.kind = false := by
    cases kind : frame.kind <;> simp only [branchLoop]
    exact False.elim (forward kind)
  have ready : false = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (0#u32)) := by
    intro impossible
    cases impossible
  have count : branchInstructionCount false frame source = 1 := by
    simp only [branchInstructionCount, width, if_pos elided,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth 0#u32 false
    ({ index := index, frame := frame, lookup := lookup, position := position } : BranchSelection compiler depth)
    (by
      intro actual interval
      have same : actual = source := by
        apply UScalar.eq_of_val_eq
        simp only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] at interval
        omega
      subst actual
      apply Or.inr
      refine ⟨law, ?_⟩
      rw [count]
      refine ⟨?_, ?_, coordinateFits, fun _ => fixupsFit⟩
      · change compiler.function.code.val.length + _ ≤ Usize.max
        omega
      · change compiler.function.source_offsets.val.length + _ ≤ Usize.max
        omega)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  change status = .Ok () at accepted
  rw [accepted] at called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 0#u32 false (.Ok ()) called
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

@[step] theorem compiler_branch_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () → ∃ fixups,
        out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        BranchHole out.2.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results ∧
        out.2.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.results core.num.U32.MAX ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1) ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · apply WP.spec_mono (branch_elided_forward ops law compiler frame index depth source lookup
      position forward elided sourcePosition fixupsFit (by omega) (by omega) coordinateFits)
    intro out effect accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect accepted
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_pos elided]
      exact ⟨site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩
  · have nonempty : frame.results ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    apply WP.spec_mono (branch_transfer_forward ops law compiler frame index depth source lookup
      position forward nonempty different sourcePosition fixupsFit codeFits offsetsFit coordinateFits)
    intro out effect accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect accepted
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_neg elided]
      exact ⟨by simp [code], site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩

end Itasca.Runtime.Compiler

end

/-! ## LoweringLoopBranch -/

section

/-! Exact backward loop-branch emission for arbitrary label depth, including
zero-arity and identity-copy elision. Loop targets are already resolved and
construct a source branch certificate without a forward-fixup assumption. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096 in
@[step] theorem branch_transfer_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [transferInstruction frame.height source frame.params, .Jump frame.start_pc] ∧
        out.2.frames = compiler.frames ⦄ := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kind]
  have loop : branchLoop frame.kind = true := by
    simp only [branchLoop, kind]
  have nonelided : ¬ (frame.params = 0#u32 ∨ source = frame.height) :=
    fun choice => choice.elim nonempty different
  have ready : false = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (0#u32)) := by
    intro impossible
    cases impossible
  have count : branchInstructionCount false frame source = 2 := by
    simp only [branchInstructionCount, width, if_neg nonelided,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth 0#u32 false
    ({ index := index, frame := frame, lookup := lookup, position := position } : BranchSelection compiler depth)
    (by
      intro actual interval
      have same : actual = source := by
        apply UScalar.eq_of_val_eq
        simp only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] at interval
        omega
      subst actual
      apply Or.inr
      refine ⟨law, ?_⟩
      rw [count]
      refine ⟨?_, ?_, coordinateFits, fun different => False.elim (different kind)⟩
      · change compiler.function.code.val.length + _ ≤ Usize.max
        omega
      · change compiler.function.source_offsets.val.length + _ ≤ Usize.max
        omega)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  change status = .Ok () at accepted
  rw [accepted] at called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 0#u32 false (.Ok ()) called
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

set_option maxRecDepth 4096 in
@[step] theorem branch_elided_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.Jump frame.start_pc] ∧
        out.2.frames = compiler.frames ⦄ := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kind]
  have loop : branchLoop frame.kind = true := by
    simp only [branchLoop, kind]
  have ready : false = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (0#u32)) := by
    intro impossible
    cases impossible
  have count : branchInstructionCount false frame source = 1 := by
    simp only [branchInstructionCount, width, if_pos elided,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth 0#u32 false
    ({ index := index, frame := frame, lookup := lookup, position := position } : BranchSelection compiler depth)
    (by
      intro actual interval
      have same : actual = source := by
        apply UScalar.eq_of_val_eq
        simp only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] at interval
        omega
      subst actual
      apply Or.inr
      refine ⟨law, ?_⟩
      rw [count]
      refine ⟨?_, ?_, coordinateFits, fun different => False.elim (different kind)⟩
      · change compiler.function.code.val.length + _ ≤ Usize.max
        omega
      · change compiler.function.source_offsets.val.length + _ ≤ Usize.max
        omega)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  change status = .Ok () at accepted
  rw [accepted] at called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 0#u32 false (.Ok ()) called
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

@[step] theorem compiler_branch_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.params frame.start_pc ∧
        out.2.frames = compiler.frames ⦄ := by
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · apply WP.spec_mono (branch_elided_loop ops law compiler frame index depth source lookup
      position kind elided sourcePosition (by omega) (by omega) coordinateFits)
    intro out effect accepted
    simpa [branchInstructions, elided] using effect accepted
  · have nonempty : frame.params ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    apply WP.spec_mono (branch_transfer_loop ops law compiler frame index depth source lookup
      position kind nonempty different sourcePosition codeFits offsetsFit coordinateFits)
    intro out effect accepted
    simpa [branchInstructions, elided] using effect accepted

end Itasca.Runtime.Compiler

end

/-! ## LoweringBranchIf -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_condition {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (condition : U32)
    (found : compiler.before.val[compiler.before.val.length - 1]? = some condition) :
    runtime.compiler.FunctionCompiler.operand ops compiler 1#usize ⦃ out => out = .Ok condition ⦄ := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have exact := (List.getElem?_eq_some_iff.mp found).2
  rw [runtime.compiler.FunctionCompiler.operand.eq]
  step with operand_at compiler.before.deref 1#usize (by simp)
    (by simpa [alloc.vec.Vec.deref] using (show 1 ≤ compiler.before.val.length by omega)) as ⟨out, effect⟩
  simpa [alloc.vec.Vec.deref, exact] using effect

set_option maxRecDepth 4096 in
@[step] theorem branch_if_elided_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.JumpIfNonZero condition core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length ∧
          out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
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
  have count : branchInstructionCount true frame source = 1 := by
    simp only [branchInstructionCount, width, if_pos elided,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth 1#u32 true
    ({ index := index, frame := frame, lookup := lookup, position := position } : BranchSelection compiler depth)
    (by
      intro actual interval
      have same : actual = source := by
        apply UScalar.eq_of_val_eq
        simp only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] at interval
        omega
      subst actual
      apply Or.inr
      refine ⟨law, ?_⟩
      rw [count]
      refine ⟨?_, ?_, coordinateFits, fun _ => fixupsFit⟩
      · change compiler.function.code.val.length + _ ≤ Usize.max
        omega
      · change compiler.function.source_offsets.val.length + _ ≤ Usize.max
        omega)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  change status = .Ok () at accepted
  rw [accepted] at called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 1#u32 true (.Ok ()) called
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

@[step] theorem branch_if_elided_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.JumpIfNonZero condition frame.start_pc] ∧
        out.2.frames = compiler.frames ⦄ := by
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kind]
  have loop : branchLoop frame.kind = true := by
    simp only [branchLoop, kind]
  have ready : true = true → runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok (condition)) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact same ▸ called
  have count : branchInstructionCount true frame source = 1 := by
    simp only [branchInstructionCount, width, if_pos elided,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth 1#u32 true
    ({ index := index, frame := frame, lookup := lookup, position := position } : BranchSelection compiler depth)
    (by
      intro actual interval
      have same : actual = source := by
        apply UScalar.eq_of_val_eq
        simp only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] at interval
        omega
      subst actual
      apply Or.inr
      refine ⟨law, ?_⟩
      rw [count]
      refine ⟨?_, ?_, coordinateFits, fun different => False.elim (different kind)⟩
      · change compiler.function.code.val.length + _ ≤ Usize.max
        omega
      · change compiler.function.source_offsets.val.length + _ ≤ Usize.max
        omega)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  change status = .Ok () at accepted
  rw [accepted] at called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 1#u32 true (.Ok ()) called
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

end Itasca.Runtime.Compiler

end

/-! ## LoweringConditionalTransfer -/

section

/-! Exact conditional branches with nonempty slot transfers. The guard skips
the copy and jump on false; the final patch fixes its exact resume address. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096 in
@[step] theorem branch_if_transfer_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length + 3)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.JumpIfZero condition resume, transferInstruction frame.height source frame.results, .Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length + 2 ∧
          out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
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
  have count : branchInstructionCount true frame source = 3 := by
    simp only [branchInstructionCount, width, if_neg nonelided,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth 1#u32 true
    ({ index := index, frame := frame, lookup := lookup, position := position } : BranchSelection compiler depth)
    (by
      intro actual interval
      have same : actual = source := by
        apply UScalar.eq_of_val_eq
        simp only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] at interval
        omega
      subst actual
      apply Or.inr
      refine ⟨law, ?_⟩
      rw [count]
      refine ⟨?_, ?_, coordinateFits, fun _ => fixupsFit⟩
      · change compiler.function.code.val.length + _ ≤ Usize.max
        omega
      · change compiler.function.source_offsets.val.length + _ ≤ Usize.max
        omega)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  change status = .Ok () at accepted
  rw [accepted] at called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 1#u32 true (.Ok ()) called
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

set_option maxRecDepth 4096 in
@[step] theorem branch_if_transfer_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length + 3)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.JumpIfZero condition resume, transferInstruction frame.height source frame.params, .Jump frame.start_pc] ∧
        out.2.frames = compiler.frames ⦄ := by
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
  have count : branchInstructionCount true frame source = 3 := by
    simp only [branchInstructionCount, width, if_neg nonelided,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth 1#u32 true
    ({ index := index, frame := frame, lookup := lookup, position := position } : BranchSelection compiler depth)
    (by
      intro actual interval
      have same : actual = source := by
        apply UScalar.eq_of_val_eq
        simp only [width, UScalar.ofNatCore_val_eq, Nat.add_zero] at interval
        omega
      subst actual
      apply Or.inr
      refine ⟨law, ?_⟩
      rw [count]
      refine ⟨?_, ?_, coordinateFits, fun different => False.elim (different kindEq)⟩
      · change compiler.function.code.val.length + _ ≤ Usize.max
        omega
      · change compiler.function.source_offsets.val.length + _ ≤ Usize.max
        omega)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  change status = .Ok () at accepted
  rw [accepted] at called
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth 1#u32 true (.Ok ()) called
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

/-! ## LoweringReturn -/

section

/-! Actual RETURN callback emission and terminal structured source certificate. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem callback_return {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (body : runtime.compiler.Frame) (source : U32)
    (reachable : compiler.reachable = true)
    (bodyFrame : compiler.frames.val[0]? = some body)
    (height : compiler.height.val = source.val + body.results.val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        out.2.function.code.val = compiler.function.code.val ++ [.Return source body.results] ∧
        out.2.frames = compiler.frames ∧ compilerLocals out.2 = compilerLocals compiler ⦄ := by
  have root : compiler.reachable = true → 0 < compiler.frames.val.length := fun _ =>
    (List.getElem?_eq_some_iff.mp bodyFrame).1
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.total ops law compiler state root codeFits sourceFits coordinateFits)
  rw [called, WP.spec_ok]
  intro accepted
  dsimp only at accepted ⊢
  subst status
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv ops compiler after state (.Ok ()) called with
  | dead dead observed => rw [reachable] at dead; cases dead
  | @emitted frame word middle _ _ live selected position emitted observed =>
    have read := alloc.vec.Vec.index_usize_spec compiler.frames 0#usize (root reachable)
    rw [alloc.vec.Vec.index_slice_index] at selected
    rw [selected, WP.spec_ok] at read
    have same : frame = body := read.trans (List.getElem?_eq_some_iff.mp bodyFrame).2
    rw [same] at position emitted
    have calculation := U32.checked_sub_bv_spec compiler.height body.results
    have positionEq : U32.checked_sub compiler.height body.results = some word := by
      change Result.ok (U32.checked_sub compiler.height body.results) = .ok (some word) at position
      exact Result.ok.injEq.mp position
    rw [positionEq] at calculation
    have wordEq : word = source := by apply UScalar.eq_of_val_eq; omega
    subst word
    obtain ⟨used, code, sources, emission, _, appended, _⟩ :=
      ((runtime.compiler.FunctionCompiler.emit.inv ops compiler middle (.Return source body.results) (.Ok ()) emitted).2 law).2 rfl
    have observation := compiler_observe_frame_raw ops {middle with reachable := false} state (.Ok ()) after observed
    rw [observation, emission]
    exact ⟨rfl, appended, rfl, rfl⟩


end Itasca.Runtime.Compiler

end

/-! ## LoweringTrap -/

section

/-!
Compilation of an unreachable instruction.

Main declarations: `callback_unreachable`. A direct consumer is `Compiler.Local.Checking.TerminalInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem callback_unreachable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (reachable : compiler.reachable = true)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops compiler state ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        out.2.function.code.val = compiler.function.code.val ++ [.Unreachable] ∧
        out.2.frames = compiler.frames ∧ out.2.function.locals = compiler.function.locals ⦄ := by
  obtain ⟨⟨reply, after⟩, called, _⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.total ops law compiler state codeFits sourceFits coordinateFits)
  rw [called, WP.spec_ok]
  intro accepted
  dsimp only at accepted ⊢
  subst reply
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops compiler after state (.Ok ()) called with
  | dead dead observed => simp only [reachable, Bool.true_eq_false] at dead
  | @emitted middle _ _ live emitted observed =>
    have frame := compiler_observe_frame_raw ops {middle with reachable := false} state (.Ok ()) after observed
    have exactEmission := ((runtime.compiler.FunctionCompiler.emit.inv ops compiler middle .Unreachable (.Ok ()) emitted).2 law).2 rfl
    obtain ⟨used, code, sources, shape, _, appended, _⟩ := exactEmission
    rw [frame, shape]
    exact ⟨rfl, appended, rfl, rfl⟩

end Itasca.Runtime.Compiler

end
