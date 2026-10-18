import Exec.Code.Local.Lowering.Common.Emit

/-! Exact branch patching and pending forward-fixup preservation. The compiler
changes only one branch target, preserves existing slot layout and code length,
and leaves every separately addressed pending fixup untouched. -/

namespace Exec.Code
open Aeneas Aeneas.Std

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
  obtain ⟨⟨instruction, back⟩, hindex, hinstruction, hback⟩ :=
    WP.spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec compiler.function.code pc index)
  have instruction_eq : instruction = kind.instruction old := hinstruction.trans found
  subst instruction
  cases kind <;>
    rw [runtime.compiler.control.FunctionCompiler.patch, alloc.vec.Vec.index_mut_slice_index,
      hindex, bind_ok, found] <;>
    simp [BranchKind.instruction, WP.spec_ok, Patched, hback, alloc.vec.Vec.set_val_eq]

theorem Patched.layout {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {pc instruction stack} (patched : Patched before after pc instruction)
    (layout : CompilerLayout before stack) : CompilerLayout after stack := by
  obtain ⟨code, rfl, hcode⟩ := patched
  exact ⟨layout.localSlots, layout.localOffsets, layout.operandOffsets,
    layout.height, layout.capacity⟩

theorem Patched.code_length {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {pc instruction} (patched : Patched before after pc instruction) :
    after.function.code.val.length = before.function.code.val.length := by
  obtain ⟨code, rfl, hcode⟩ := patched
  simp [hcode]

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

/-- Each pending forward fixup denotes an actual placeholder branch, including
its condition slot for conditional branches. -/
def PendingFixups (code : List runtime.bytecode.Instr) (pending : List (Nat × BranchKind)) : Prop :=
  ∀ entry, entry ∈ pending → code[entry.1]? = some (entry.2.instruction core.num.U32.MAX)

theorem Patched.pending {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {pc instruction pending} (patched : Patched before after pc instruction)
    (old : PendingFixups before.function.code.val pending)
    (separate : ∀ entry, entry ∈ pending → entry.1 ≠ pc) :
    PendingFixups after.function.code.val pending := by
  intro entry member
  rw [patched.other (separate entry member)]
  exact old entry member

end Exec.Code
