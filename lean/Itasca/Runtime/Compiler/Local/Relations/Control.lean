import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Support.Result

/-! Exact branch patching and pending forward-fixup preservation. The compiler
changes only one branch target, preserves existing slot layout and code length,
and leaves every separately addressed pending fixup untouched. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

inductive BranchKind where
  | jump
  | zero (condition : U32)
  | nonzero (condition : U32)

def BranchKind.instruction : BranchKind → U32 → runtime.bytecode.Instr
  | .jump, target => .Jump target
  | .zero condition, target => .JumpIfZero condition target
  | .nonzero condition, target => .JumpIfNonZero condition target

def Patched {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (pc : Nat) (instruction : runtime.bytecode.Instr) : Prop :=
  ∃ code, after = { before with function := { before.function with code } } ∧
    code.val = before.function.code.val.set pc instruction

/-- Every normal patch return either rejects unchanged or records its exact retarget operation. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.patch.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (pc : Usize) (target : U32) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    (status = .Err Itasca.error.VisitError.OutOfMemory ∧ after = before) ∨
      ∃ original replacement, status = .Ok () ∧
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.bytecode.Instr)
          before.function.code pc = .ok original ∧
        runtime.bytecode.Instr.retarget original target = .ok (some replacement) ∧
        Patched before after pc.val replacement := by
  unfold runtime.compiler.control.FunctionCompiler.patch at accepted
  obtain ⟨original, read, rest⟩ := bind_ok_inv _ _ _ accepted
  obtain ⟨patched, retargeted, rest⟩ := bind_ok_inv _ _ _ rest
  cases patched with
  | none =>
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact Or.inl ⟨rest.1.symm, rest.2.symm⟩
  | some instruction =>
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨old, restore⟩, indexed, rest⟩ := bind_ok_inv _ _ _ rest
    rw [alloc.vec.Vec.index_mut_slice_index] at indexed
    unfold alloc.vec.Vec.index_mut_usize at indexed
    obtain ⟨found, foundEq, indexed⟩ := bind_ok_inv _ _ _ indexed
    obtain ⟨oldEq, rfl⟩ := Prod.mk.inj (Result.ok.injEq.mp indexed)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.injEq.mp rest)
    exact Or.inr ⟨original, instruction, rfl, read, retargeted, _, rfl,
      by simp only [alloc.vec.Vec.set_val_eq]⟩

theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.patch.available {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (pc : Usize)
    (kind : BranchKind) (old target : U32)
    (atPc : compiler.function.code.val[pc.val]? = some (kind.instruction old)) :
    runtime.compiler.control.FunctionCompiler.patch ops compiler pc target ⦃ out =>
      out.1 = .Ok () ∧ Patched compiler out.2 pc.val (kind.instruction target) ⦄ := by
  have index := (List.getElem?_eq_some_iff.mp atPc).1
  have found := (List.getElem?_eq_some_iff.mp atPc).2
  obtain ⟨instruction, hread, hinstruction⟩ :=
    WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec compiler.function.code pc index)
  obtain ⟨⟨_, back⟩, hindex, _, hback⟩ :=
    WP.spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec compiler.function.code pc index)
  rw [hinstruction.trans found] at hread
  rw [runtime.compiler.control.FunctionCompiler.patch, alloc.vec.Vec.index_slice_index, hread,
    bind_ok, alloc.vec.Vec.index_mut_slice_index, hindex]
  cases kind <;>
    simp only [BranchKind.instruction, runtime.bytecode.Instr.retarget, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, WP.spec_ok, Patched, hback,
      bind_ok, uncurry_apply_pair, true_and]
  all_goals exact ⟨_, rfl, by simp only [alloc.vec.Vec.set_val_eq]⟩


/-- A known branch site admits a normal patch return, without an allocator law. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.patch.total {A : Type}
    (ops : runtime.platform.Alloc A) (compiler : runtime.compiler.FunctionCompiler A)
    (pc : Usize) (kind : BranchKind) (old target : U32)
    (atPc : compiler.function.code.val[pc.val]? = some (kind.instruction old)) :
    runtime.compiler.control.FunctionCompiler.patch ops compiler pc target ⦃ _ => True ⦄ := by
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.patch.available ops compiler pc kind old target atPc)
  intro out effect
  trivial

@[step] theorem compiler_patch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (pc : Usize)
    (kind : BranchKind) (old target : U32)
    (atPc : compiler.function.code.val[pc.val]? = some (kind.instruction old)) :
    runtime.compiler.control.FunctionCompiler.patch ops compiler pc target ⦃ out =>
      out.1 = .Ok () ∧ Patched compiler out.2 pc.val (kind.instruction target) ⦄ := by
  exact runtime.compiler.control.FunctionCompiler.patch.available ops compiler pc kind old target atPc

/-- A patch either rejects without changing the compiler or replaces exactly
one instruction. -/
theorem compiler_patch_cases {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target =
      .ok (status, after)) :
    after = before ∨ ∃ instruction, Patched before after pc.val instruction := by
  rcases runtime.compiler.control.FunctionCompiler.patch.inv ops before after pc target status accepted with
    rejected | ⟨original, replacement, success, read, retargeted, patched⟩
  · exact Or.inl rejected.2
  · exact Or.inr ⟨replacement, patched⟩

theorem Patched.target {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {pc instruction} (patched : Patched before after pc instruction)
    (inside : pc < before.function.code.val.length) :
    after.function.code.val[pc]? = some instruction := by
  obtain ⟨code, rfl, hcode⟩ := patched
  simp [hcode, inside]

theorem Patched.other {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {pc instruction index} (patched : Patched before after pc instruction)
    (different : index ≠ pc) :
    after.function.code.val[index]? = before.function.code.val[index]? := by
  obtain ⟨code, rfl, hcode⟩ := patched
  simp [hcode, Ne.symm different]

end Itasca.Runtime.Compiler
