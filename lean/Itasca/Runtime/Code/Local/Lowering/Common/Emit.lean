import Itasca.Runtime.Code.Local.Relations.Common.LayoutProofs
import Itasca.Runtime.Code.Local.Relations.Common.CompileInv

/-! Kernel-checked compiler primitives: PC conversion, instruction charging,
operand lookup, and exact emission. Emission records source coordinates and
preserves all state except the budget and the two appended vectors. -/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_pc {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) :
    runtime.compiler.FunctionCompiler.pc ops compiler ⦃ out =>
      out.2.function = compiler.function ∧
      (∀ word, out.1 = .Ok word → word.val = compiler.function.code.val.length) ∧
      (∃ budget, out.2 = { compiler with budget }) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.pc
  step*
  all_goals simp [runtime.compiler.Budget.reject]
  refine ⟨?_, ⟨compiler.budget, rfl⟩⟩
  simp_all [core.num.U32.MAX, U32.rMax]
  scalar_tac

@[step] theorem charge_instruction {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Instructions ⦃ out =>
      out.2.limits = budget.limits ∧
      (out.1 = .Ok () → out.2.instructions.val = budget.instructions.val + 1) ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject, WP.spec_ok]
  · step
    simp_all

@[step] theorem compiler_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (stack : List valtype)
    (layout : CompilerLayout compiler stack) (depth : Usize)
    (positive : 0 < depth.val) (fits : depth.val ≤ stack.length) :
    runtime.compiler.FunctionCompiler.operand ops compiler depth ⦃ result =>
      ∃ word, result = .Ok word ∧ word.val =
        slots (compilerLocals compiler) + offset stack (stack.length - depth.val) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.operand
  have length := layout.operands_length
  have cap : depth.val ≤ compiler.before.val.length := by omega
  step with operand_at compiler.before.deref depth positive (by simpa [alloc.vec.Vec.deref] using cap) as ⟨r, hr⟩
  refine ⟨_, hr, ?_⟩
  have index : stack.length - depth.val < stack.length := by omega
  have mapped := congrArg (fun list => list[stack.length - depth.val]?) layout.operandOffsets
  simpa [stackOffsets, List.getElem?_map, List.getElem?_eq_getElem, index, length,
    alloc.vec.Vec.deref] using mapped

/-- Successful emission appends one instruction and its source coordinate, and
only changes the budget and those two vectors. -/
def Emitted {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) : Prop :=
  ∃ budget code sources,
    after = { before with budget, function := { before.function with code, source_offsets := sources } } ∧
    code.val = before.function.code.val ++ [instruction] ∧
    sources.val.map (fun word => word.val) =
      before.function.source_offsets.val.map (fun word => word.val) ++
        [before.function.body_start.val + before.next_source.val]

@[step] theorem compiler_emit {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ out =>
      out.1 = .Ok () → Emitted compiler out.2 instruction ⦄ := by
  unfold runtime.compiler.FunctionCompiler.emit
  step with compiler_pc ops compiler as ⟨r, c, hf, hp, budget, hc⟩
  subst c
  cases r with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok word =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with charge_instruction ops budget as ⟨r1, b, hb⟩
    cases r1 with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      simp only [bind_ok]
      step with budget_push ops law b compiler.function.code instruction codeFits as
        ⟨r2, b1, code, hcode⟩
      rcases hcode with ⟨rfl, rfl, hcode⟩ | ⟨rfl, rfl, herror⟩
      · simp only [bind_ok]
        step as ⟨offset, hoff⟩
        step with budget_push ops law b1 compiler.function.source_offsets offset sourceFits as
          ⟨r3, b2, sources, hsources⟩
        rcases hsources with ⟨rfl, rfl, hsources⟩ | ⟨rfl, rfl, herror⟩
        · intro _
          refine ⟨_, _, _, rfl, hcode, ?_⟩
          simp [hsources, hoff]
        · simp
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem Emitted.layout {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction stack} (emitted : Emitted before after instruction)
    (layout : CompilerLayout before stack) : CompilerLayout after stack := by
  obtain ⟨budget, code, sources, rfl, _, _⟩ := emitted
  exact ⟨layout.localSlots, layout.localOffsets, layout.operandOffsets,
    layout.height, layout.capacity⟩

theorem Emitted.old_instruction {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction old} {index : Nat} (emitted : Emitted before after instruction)
    (previous : before.function.code.val[index]? = some old) :
    after.function.code.val[index]? = some old := by
  obtain ⟨budget, code, sources, rfl, hcode, _⟩ := emitted
  simp only [hcode]
  exact List.getElem?_append_left (List.getElem?_eq_some_iff.mp previous).1 |>.trans previous

end Itasca.Runtime.Code
