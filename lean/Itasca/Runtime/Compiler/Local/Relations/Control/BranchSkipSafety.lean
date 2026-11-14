import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds

/-!
Safety of skipped forward and loop branches, combining the distinct branch encodings under one callback safety argument.
-/

/-! ## Branch Skip Forward Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxRecDepth 4096 in
@[step] theorem branch_transfer_forward_with_skip {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
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
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth skip false
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
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth skip false (.Ok ()) called
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
@[step] theorem branch_elided_forward_with_skip {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
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
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth skip false
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
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth skip false (.Ok ()) called
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

/-! ## Branch Skip Loop Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxRecDepth 4096 in
@[step] theorem branch_transfer_loop_with_skip {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
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
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth skip false
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
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth skip false (.Ok ()) called
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
@[step] theorem branch_elided_loop_with_skip {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
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
  have normal := runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth skip false
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
  have effect := runtime.compiler.control.FunctionCompiler.branch.inv ops compiler after depth skip false (.Ok ()) called
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

/-! ## Branch Skip Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

private theorem branch_skip_underflow_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (frame : runtime.compiler.Frame)
    (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (underflow : compiler.height.val <
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val + skip.val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ _ => True ⦄ := by
  apply runtime.compiler.control.FunctionCompiler.branch.total ops compiler depth skip false
    ⟨index, frame, lookup, position⟩
  intro source sourcePosition
  change compiler.height.val < (branchWidth frame).val + skip.val at underflow
  dsimp only at sourcePosition
  omega

@[step] theorem compiler_branch_skip_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ _ => True ⦄ := by
  by_cases loop : frame.kind = Itasca.code.LabelKind.Loop
  · by_cases enough : frame.params.val + skip.val ≤ compiler.height.val
    · let source := U32.ofNatCore (compiler.height.val - (frame.params.val + skip.val))
        (by have := compiler.height.hBounds; omega)
      have sourceValue : source.val + frame.params.val + skip.val = compiler.height.val := by
        change compiler.height.val - (frame.params.val + skip.val) + frame.params.val + skip.val = compiler.height.val
        omega
      by_cases empty : frame.params = 0#u32
      · apply WP.spec_mono (branch_elided_loop_with_skip ops law compiler frame index depth source skip
          lookup position loop (.inl empty) sourceValue (by omega) (by omega) coordinateFits)
        simp
      · by_cases same : source = frame.height
        · apply WP.spec_mono (branch_elided_loop_with_skip ops law compiler frame index depth source skip
            lookup position loop (.inr same) sourceValue (by omega) (by omega) coordinateFits)
          simp
        · apply WP.spec_mono (branch_transfer_loop_with_skip ops law compiler frame index depth source skip
            lookup position loop empty same sourceValue codeFits sourceFits coordinateFits)
          simp
    · exact branch_skip_underflow_total ops compiler frame index depth skip lookup position (by simp [loop]; omega)
  · by_cases enough : frame.results.val + skip.val ≤ compiler.height.val
    · let source := U32.ofNatCore (compiler.height.val - (frame.results.val + skip.val))
        (by have := compiler.height.hBounds; omega)
      have sourceValue : source.val + frame.results.val + skip.val = compiler.height.val := by
        change compiler.height.val - (frame.results.val + skip.val) + frame.results.val + skip.val = compiler.height.val
        omega
      by_cases empty : frame.results = 0#u32
      · apply WP.spec_mono (branch_elided_forward_with_skip ops law compiler frame index depth source skip
          lookup position loop (.inl empty) sourceValue fixupsFit (by omega) (by omega) coordinateFits)
        simp
      · by_cases same : source = frame.height
        · apply WP.spec_mono (branch_elided_forward_with_skip ops law compiler frame index depth source skip
            lookup position loop (.inr same) sourceValue fixupsFit (by omega) (by omega) coordinateFits)
          simp
        · apply WP.spec_mono (branch_transfer_forward_with_skip ops law compiler frame index depth source skip
            lookup position loop empty same sourceValue fixupsFit codeFits sourceFits coordinateFits)
          simp
    · exact branch_skip_underflow_total ops compiler frame index depth skip lookup position
        (by cases kindEq : frame.kind <;> simp_all)
end Itasca.Runtime.Compiler

end
