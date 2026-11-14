import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Runtime.Compiler.Local.Relations.Layout.CompileInv

/-! Kernel-checked compiler primitives: PC conversion, instruction charging,
operand lookup, and exact emission. Emission records source coordinates and
preserves all state except the budget and the two appended vectors. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

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

@[step] theorem compiler_operand_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (depth : Usize) :
    runtime.compiler.FunctionCompiler.operand ops compiler depth ⦃ out =>
      ∀ word, out = .Ok word → word ∈ compiler.before.val ⦄ := by
  simpa [runtime.compiler.FunctionCompiler.operand, alloc.vec.Vec.deref] using
    operand_at_total compiler.before.deref depth

/-- A representable bytecode PC excludes the actual instruction-index rejection. -/
theorem compiler_pc_available {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A)
    (bounded : compiler.function.code.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.pc ops compiler ⦃ out =>
      out.2 = compiler ∧ ∃ pc, out.1 = .Ok pc ∧ pc.val = compiler.function.code.length ⦄ := by
  unfold runtime.compiler.FunctionCompiler.pc
  step as ⟨maximum,maximumEq⟩
  have inside : ¬ alloc.vec.Vec.len compiler.function.code > maximum := by
    simp_all [core.num.U32.MAX,U32.rMax]
    scalar_tac
  simp only [if_neg inside]
  step as ⟨pc,pcEq⟩
  refine ⟨pc,rfl,?_⟩
  simp only [pcEq,UScalar.cast_val_eq]
  scalar_tac

/-- Frame facts hold even when an arbitrary allocator changes vector contents. -/
def EmitFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget,
    function := {before.function with code := after.function.code, source_offsets := after.function.source_offsets}}

/-- Successful emission appends the instruction and its source coordinate, and
charges exactly one instruction while preserving every other field. -/
def EmittedExact {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) : Prop :=
  ∃ used code sources,
    after = {before with
      budget := {before.budget with instructions := used},
      function := {before.function with code, source_offsets := sources}} ∧
    used.val = before.budget.instructions.val + 1 ∧
    code.val = before.function.code.val ++ [instruction] ∧
    sources.val.map (fun word => word.val) = before.function.source_offsets.val.map (fun word => word.val) ++
      [before.function.body_start.val + before.next_source.val]

theorem charge_instruction_exact {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Instructions ⦃ (status, after) =>
      status = .Ok () → ∃ used, after = {budget with instructions := used} ∧
        used.val = budget.instructions.val + 1 ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp only [runtime.compiler.Budget.reject, bind_ok, WP.spec_ok, uncurry_apply_pair,
      reduceCtorEq, false_implies]
  · step as ⟨used, added⟩
    intro _
    exact ⟨used, rfl, added⟩

/-- Every normal return preserves the frame without allocator assumptions.
Allocator correctness additionally gives code growth and the exact success effect. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.emit.inv {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    EmitFrame before after ∧ (Platform.AllocCorrect ops →
      (after.function.code.val = before.function.code.val ∨ after.function.code.val = before.function.code.val ++ [instruction]) ∧
      (status = .Ok () → EmittedExact before after instruction)) := by
  unfold runtime.compiler.FunctionCompiler.emit at called
  obtain ⟨⟨pc, current⟩, pcRun, rest⟩ := bind_ok_inv _ _ _ called
  have pcEffect := compiler_pc ops before
  rw [pcRun, WP.spec_ok] at pcEffect
  cases pc with
  | Err error =>
    obtain ⟨_, _, budget, currentEq⟩ := pcEffect
    change current = {before with budget} at currentEq
    subst current
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨rfl, rfl⟩ := rest
    exact ⟨rfl, fun _ => ⟨Or.inl rfl, by intro impossible; cases impossible⟩⟩
  | Ok word =>
    have pcBound : before.function.code.length ≤ U32.max := by
      have exactPc := pcEffect.2.1 word rfl
      scalar_tac
    have pcSame := compiler_pc_available ops before pcBound
    rw [pcRun, WP.spec_ok] at pcSame
    have same := pcSame.1
    change current = before at same
    subst current
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨charged, budget1⟩, chargeRun, rest⟩ := bind_ok_inv _ _ _ rest
    cases charged with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      exact ⟨rfl, fun _ => ⟨Or.inl rfl, by intro impossible; cases impossible⟩⟩
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨pushed, budget2, code⟩, pushRun, rest⟩ := bind_ok_inv _ _ _ rest
      cases pushed with
      | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        refine ⟨rfl, fun law => ⟨?_, by intro impossible; cases impossible⟩⟩
        exact budget_push_code_result ops law budget1 budget2 before.function.code code instruction (.Err error) pushRun
      | Ok value =>
        cases value
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨coordinate, coordinateRun, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨⟨result, budget3, sources⟩, sourcesRun, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        refine ⟨rfl, fun law => ?_⟩
        have codeEffect := budget_push_success ops law budget1 budget2 before.function.code code instruction pushRun
        refine ⟨Or.inr codeEffect.2, ?_⟩
        intro accepted
        subst result
        have sourcesEffect := budget_push_success ops law budget2 budget3 before.function.source_offsets sources coordinate sourcesRun
        have chargedEffect := charge_instruction_exact ops before.budget
        rw [chargeRun, WP.spec_ok] at chargedEffect
        obtain ⟨used, budgetEq, usedEq⟩ := chargedEffect rfl
        have coordinateEq := control_add_success coordinateRun
        refine ⟨used, code, sources, ?_, usedEq, codeEffect.2, ?_⟩
        · rw [sourcesEffect.1, codeEffect.1, budgetEq]
        · simp only [sourcesEffect.2, List.map_append, List.map_cons, List.map_nil, coordinateEq]

/-- Accepted instruction charging modifies exactly the instruction counter. -/
theorem charge_instruction_available_exact {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.instructions.val < budget.limits.max_instructions.val) :
    runtime.compiler.Budget.charge ops budget .Instructions ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after = {budget with instructions := used} ∧
        used.val = budget.instructions.val + 1 ⦄ := by
  have notFull : ¬budget.instructions ≥ budget.limits.max_instructions := by scalar_tac
  simp only [runtime.compiler.Budget.charge, if_neg notFull]
  step as ⟨used, added⟩
  exact ⟨used, rfl, added⟩

/-- Correct allocation and representable vector lengths and coordinates exclude
extracted failure; ordinary Rust errors remain possible. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.emit.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.emit
  step with compiler_pc ops compiler as ⟨r, c, hf, hp, budget, hc⟩
  subst c
  cases r with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
  | Ok word =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with charge_instruction ops budget as ⟨r1, b, hb⟩
    cases r1 with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with budget_push ops law b compiler.function.code instruction codeFits as
        ⟨r2, b1, code, hcode⟩
      rcases hcode with ⟨rfl, rfl, hcode⟩ | ⟨rfl, rfl, herror⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨offset, hoff⟩
        step with budget_push ops law b1 compiler.function.source_offsets offset sourceFits as
          ⟨r3, b2, sources, hsources⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]

/-- Available allocation and sufficient instruction budget guarantee successful
emission with its exact state effect. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.emit.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (pcBound : compiler.function.code.length ≤ U32.max)
    (codeFits : compiler.function.code.length < Usize.max)
    (sourcesFit : compiler.function.source_offsets.length < Usize.max)
    (codeRequest : compiler.function.code.length+1 ≤ bound)
    (sourceRequest : compiler.function.source_offsets.length+1 ≤ bound)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (room : compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ (status, after) =>
      status = .Ok () ∧ EmittedExact compiler after instruction ⦄ := by
  unfold runtime.compiler.FunctionCompiler.emit
  step with compiler_pc_available ops compiler pcBound as ⟨status,first,same,pc,accepted,pcEq⟩
  subst first
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with charge_instruction_available_exact ops compiler.budget room
    as ⟨status, charged, accepted, used, same, usedEq⟩
  rw [accepted]
  subst charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with budget_push_available ops bound available {compiler.budget with instructions := used}
    compiler.function.code instruction codeFits codeRequest
    as ⟨status,charged,code,accepted,same,appended⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step as ⟨source,sourceEq⟩
  step with budget_push_available ops bound available {compiler.budget with instructions := used}
    compiler.function.source_offsets source sourcesFit sourceRequest
    as ⟨status,charged,sources,accepted,same,recorded⟩
  refine ⟨accepted, used, code, sources, ?_, usedEq, appended, ?_⟩
  · rw [same]
  · simp only [recorded, sourceEq, List.map_append, List.map_cons, List.map_nil]

theorem EmittedExact.emitted {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (effect : EmittedExact before after instruction) :
    Emitted before after instruction := by
  obtain ⟨used, code, sources, same, _, appended, coordinates⟩ := effect
  exact ⟨_, code, sources, same, appended, coordinates⟩

@[step] theorem compiler_emit {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ out =>
      out.1 = .Ok () → Emitted compiler out.2 instruction ⦄ := by
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.emit.total ops law compiler instruction codeFits sourceFits coordinateFits)
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  exact (((runtime.compiler.FunctionCompiler.emit.inv ops compiler after instruction status called).2 law).2 accepted).emitted

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

end Itasca.Runtime.Compiler
