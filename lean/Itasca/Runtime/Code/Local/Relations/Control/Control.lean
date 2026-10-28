import Itasca.Runtime.Code.Local.Lowering.Common.Emit
import Itasca.Support.Result

/-! Exact branch patching and pending forward-fixup preservation. The compiler
changes only one branch target, preserves existing slot layout and code length,
and leaves every separately addressed pending fixup untouched. -/

namespace Itasca.Runtime.Code
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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
@[step] theorem compiler_patch {A : Type} (ops : runtime.platform.Alloc A)
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
    simp [BranchKind.instruction, runtime.bytecode.Instr.retarget, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, WP.spec_ok, Patched, hback,
      alloc.vec.Vec.set_val_eq]

/-- A patch either rejects without changing the compiler or replaces exactly
one instruction. -/
theorem compiler_patch_cases {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target =
      .ok (status, after)) :
    after = before ∨ ∃ instruction, Patched before after pc.val instruction := by
  unfold runtime.compiler.control.FunctionCompiler.patch at accepted
  obtain ⟨_, _, rest⟩ := bind_ok_inv _ _ _ accepted
  obtain ⟨patched, _, rest⟩ := bind_ok_inv _ _ _ rest
  cases patched with
  | none =>
    left
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact rest.2.symm
  | some instruction =>
    right
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      bind_ok] at rest
    obtain ⟨⟨_, restore⟩, indexed, rest⟩ := bind_ok_inv _ _ _ rest
    rw [alloc.vec.Vec.index_mut_slice_index] at indexed
    unfold alloc.vec.Vec.index_mut_usize at indexed
    obtain ⟨_, _, indexed⟩ := bind_ok_inv _ _ _ indexed
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Result.ok.injEq.mp indexed)
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Result.ok.injEq.mp rest)
    exact ⟨instruction, _, rfl, by simp [alloc.vec.Vec.set_val_eq]⟩

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

end Itasca.Runtime.Code
