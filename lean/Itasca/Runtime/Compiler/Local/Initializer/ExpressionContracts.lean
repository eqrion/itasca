import Itasca.Runtime.Compiler.Local.Initializer.ConstantContracts
import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedTotal

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

def initializerSeed (ty : Itasca.wasm_types.ValueType) : runtime.bytecode.CompiledFunction :=
  { locals := alloc.vec.Vec.new _, local_slots := 0#u32, param_slots := 0#u32,
    slot_count := initializerWidth ty, max_stack := 0#usize, code := alloc.vec.Vec.new _,
    jump_tables := alloc.vec.Vec.new _, v128_pool := alloc.vec.Vec.new _,
    indirect := alloc.vec.Vec.new _, simd := alloc.vec.Vec.new _, source_offsets := alloc.vec.Vec.new _,
    controls := alloc.vec.Vec.new _, type_index := 0#u32, body_start := 0#usize, body_end := 0#usize }

theorem initializer_synthetic (ty : Itasca.wasm_types.ValueType) :
    runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) (initializerWidth ty) =
      .ok (initializerSeed ty) := rfl

private theorem slots_fit_zero (function : runtime.bytecode.CompiledFunction) (count : U32)
    (bounded : count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function 0#u32 count = .ok true := by
  have below : 0#u32 ≤ function.slot_count := by scalar_tac
  simp only [runtime.bytecode.CompiledFunction.slots_fit,if_pos below]
  have check : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 count
      ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    simp only [if_pos below]
    step as ⟨left,equal⟩
    have fits : count ≤ left := by scalar_tac
    simp [fits]
  obtain ⟨result,actual,rfl⟩ := WP.spec_imp_exists check
  exact actual

/-- The only extra width condition is independently visible in the source:
a vector literal requires a vector result slot. Other constant-expression
forms fit the width selected from their result type. -/
theorem initial_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (instruction : runtime.bytecode.Instr)
    (lowered : InitialInstruction function expr ty instruction)
    (capacity : function.slot_count = initializerWidth ty)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  have scalar : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 1#u32 = .ok true := by
    apply slots_fit_zero
    rw [capacity]
    cases ty <;> decide
  have wide (same : ty = .V128) :
      runtime.bytecode.CompiledFunction.slots_fit function 0#u32 2#u32 = .ok true := by
    apply slots_fit_zero
    simp [capacity,same,initializerWidth]
  cases lowered <;>
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
      runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,
      runtime.bytecode.CompiledFunction.other_valid,bind_ok]
  all_goals first | exact scalar | exact wide rfl | skip
  rename_i lo hi pool embedded
  rw [wide (vector lo hi rfl),bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp embedded).1
  have poolBound : UScalar.cast .Usize pool < alloc.vec.Vec.len function.v128_pool := by scalar_tac
  simpa [lift] using inside

/-- Exact initializer code and source metadata imply the actual publication
checker accepts. Component checker success is derived here, not assumed. -/
theorem initializer_well_formed (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (shape : InitializerCode function expr ty)
    (start : function.body_start = 0#usize) (finish : function.body_end = 0#usize)
    (offsets : function.source_offsets.val = []) (jumps : function.jump_tables.val = [])
    (controls : function.controls.val = [])
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ := by
  obtain ⟨instruction,lowered,code⟩ := shape.code
  have length : function.code.length = 2 := by simp [alloc.vec.Vec.length,code]
  apply well_formed_synthetic_accepts function start finish (by omega) offsets
    (by rw [shape.localSlots,shape.capacity]; cases ty <;> decide)
    (by rw [shape.paramSlots,shape.localSlots]) 0#u32 (initializerWidth ty)
  · simp [length,code]
  · intro j bounded
    rw [length] at bounded
    have first := initial_instruction_accepts function expr ty instruction lowered shape.capacity vector
    have returned : runtime.bytecode.CompiledFunction.instruction_valid function
        (.Return 0#u32 (initializerWidth ty)) = .ok true := by
      simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,
      runtime.bytecode.CompiledFunction.other_valid,bind_ok]
      exact slots_fit_zero function (initializerWidth ty) (by rw [shape.capacity])
    interval_cases j <;> simpa [code] using (by assumption)
  · simp [jumps]
  · simp [controls]


/-- Successful constant and return emission, prior to the publication checker. -/
structure InitializerExpressionPrefix {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) where
  constantBudget : runtime.compiler.Budget A
  function : runtime.bytecode.CompiledFunction
  returnBudget : runtime.compiler.Budget A
  code : alloc.vec.Vec runtime.bytecode.Instr
  constantCalled : runtime.compiler.initialize.constant ops budget (initializerSeed ty) expr ty 0#u32 =
    .ok (.Ok (), constantBudget, function)
  returnCalled : runtime.compiler.initialize.emit ops constantBudget function.code
    (.Return 0#u32 (initializerWidth ty)) = .ok (.Ok (), returnBudget, code)

def InitializerExpressionPrefix.result {A : Type} {ops : runtime.platform.Alloc A}
    {budget : runtime.compiler.Budget A} {expr ty} (stages : InitializerExpressionPrefix ops budget expr ty) :
    runtime.bytecode.CompiledFunction := {stages.function with code := stages.code}

/-- Exact normal-return stages of initializer expression publication. -/
inductive InitializerExpressionEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) :
    core.result.Result Usize Itasca.error.VisitError → runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop where
  | constantRejected {error afterBudget function}
      (called : runtime.compiler.initialize.constant ops budget (initializerSeed ty) expr ty 0#u32 =
        .ok (.Err error, afterBudget, function)) :
      InitializerExpressionEffect ops before budget expr ty (.Err error) before afterBudget
  | returnRejected {error constantBudget function afterBudget code}
      (constantCalled : runtime.compiler.initialize.constant ops budget (initializerSeed ty) expr ty 0#u32 =
        .ok (.Ok (), constantBudget, function))
      (returnCalled : runtime.compiler.initialize.emit ops constantBudget function.code
        (.Return 0#u32 (initializerWidth ty)) = .ok (.Err error, afterBudget, code)) :
      InitializerExpressionEffect ops before budget expr ty (.Err error) before afterBudget
  | checkerRejected (stages : InitializerExpressionPrefix ops budget expr ty)
      (checked : runtime.bytecode.CompiledFunction.well_formed stages.result = .ok false) :
      InitializerExpressionEffect ops before budget expr ty (.Err .OutOfMemory) before stages.returnBudget
  | published (stages : InitializerExpressionPrefix ops budget expr ty) {afterBudget functions}
      (checked : runtime.bytecode.CompiledFunction.well_formed stages.result = .ok true)
      (pushed : runtime.compiler.Budget.push ops stages.returnBudget before.functions stages.result =
        .ok (.Ok (), afterBudget, functions)) :
      InitializerExpressionEffect ops before budget expr ty (.Ok (alloc.vec.Vec.len before.functions))
        {before with functions} afterBudget
  | publicationRejected (stages : InitializerExpressionPrefix ops budget expr ty) {error afterBudget functions}
      (checked : runtime.bytecode.CompiledFunction.well_formed stages.result = .ok true)
      (pushed : runtime.compiler.Budget.push ops stages.returnBudget before.functions stages.result =
        .ok (.Err error, afterBudget, functions)) :
      InitializerExpressionEffect ops before budget expr ty (.Err error) {before with functions} afterBudget

 theorem _root_.Itasca.runtime.compiler.initialize.expression.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (status : core.result.Result Usize Itasca.error.VisitError)
    (called : runtime.compiler.initialize.expression ops before budget expr ty = .ok (status, after, afterBudget)) :
    InitializerExpressionEffect ops before budget expr ty status after afterBudget := by
  unfold runtime.compiler.initialize.expression at called
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok] at called
  obtain ⟨⟨constantStatus, constantBudget, function⟩, constantCalled, tail⟩ := bind_ok_inv _ _ _ called
  cases constantStatus with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .constantRejected constantCalled
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨returnStatus, returnBudget, code⟩, returnCalled, tail⟩ := bind_ok_inv _ _ _ tail
    cases returnStatus with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl, rfl⟩ := tail
      exact .returnRejected constantCalled returnCalled
    | Ok unitValue =>
      cases unitValue
      let stages : InitializerExpressionPrefix ops budget expr ty :=
        ⟨constantBudget, function, returnBudget, code, constantCalled, returnCalled⟩
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
      obtain ⟨valid, checked, tail⟩ := bind_ok_inv _ _ _ tail
      cases valid with
      | false =>
        simp only [Bool.false_eq_true, ite_false, Result.ok.injEq, Prod.mk.injEq] at tail
        obtain ⟨rfl, rfl, rfl⟩ := tail
        exact .checkerRejected stages checked
      | true =>
        simp only [ite_true] at tail
        obtain ⟨⟨pushedStatus, pushedBudget, functions⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
        cases pushedStatus with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact .publicationRejected stages checked pushed
        | Ok unitValue =>
          cases unitValue
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            bind_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact .published stages checked pushed

theorem InitializerExpressionPrefix.certified {A : Type} {ops : runtime.platform.Alloc A}
    {budget : runtime.compiler.Budget A} {expr ty}
    (stages : InitializerExpressionPrefix ops budget expr ty) (law : Platform.AllocCorrect ops) :
    InitializerCode stages.result expr ty := by
  have lowered := (runtime.compiler.initialize.constant.inv ops budget stages.constantBudget
    (initializerSeed ty) stages.function expr ty 0#u32 (.Ok ()) stages.constantCalled).success law
  have returned := (runtime.compiler.initialize.emit.inv ops stages.constantBudget stages.returnBudget
    stages.function.code stages.code (.Return 0#u32 (initializerWidth ty)) (.Ok ()) stages.returnCalled).success law
  obtain ⟨code, pool, instruction, frame, appended, certified⟩ := lowered
  have finalCertified : ConstantInstruction stages.result 0#u32 expr ty instruction :=
    ConstantInstruction.change_code (after := stages.result) certified rfl
  have finalCode : stages.result.code.val = [instruction, .Return 0#u32 (initializerWidth ty)] := by
    change stages.code.val = [instruction, .Return 0#u32 (initializerWidth ty)]
    rw [returned, frame]
    have codeEq : code.val = [instruction] := by
      simpa only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] using appended
    rw [codeEq]
    rfl

  refine ⟨⟨instruction, finalCertified, finalCode⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp only [InitializerExpressionPrefix.result, frame, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]

theorem InitializerExpressionEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {expr ty status}
    (effect : InitializerExpressionEffect ops before budget expr ty status after afterBudget) :
    after = {before with functions := after.functions} := by
  cases effect <;> rfl

theorem InitializerExpressionEffect.growth {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {expr ty status}
    (effect : InitializerExpressionEffect ops before budget expr ty status after afterBudget)
    (law : Platform.AllocCorrect ops) : after.functions.val.length ≤ before.functions.val.length + 1 := by
  cases effect with
  | constantRejected called => omega
  | returnRejected constantCalled returnCalled => omega
  | checkerRejected stages checked => omega
  | published stages checked pushed | publicationRejected stages checked pushed =>
    have changed := budget_push_code_result ops law _ _ _ _ _ _ pushed
    rcases changed with same | appended
    · simp only [same]
      omega
    · simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]

theorem InitializerExpressionEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {expr ty index}
    (effect : InitializerExpressionEffect ops before budget expr ty (.Ok index) after afterBudget)
    (law : Platform.AllocCorrect ops) :
    ∃ function, InitializerCode function expr ty ∧ index.val = before.functions.val.length ∧
      after = {before with functions := after.functions} ∧
      after.functions.val = before.functions.val ++ [function] := by
  cases effect with
  | published stages checked pushed =>
    exact ⟨stages.result, stages.certified law, rfl, rfl, (budget_push_success ops law _ _ _ _ _ pushed).2⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.expression.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (fits : module.functions.length < Usize.max) :
    runtime.compiler.initialize.expression ops module budget expr ty ⦃ _ => True ⦄ := by
  unfold runtime.compiler.initialize.expression
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok]
  have codeFits : (initializerSeed ty).code.val.length < Usize.max := by
    simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil]
    scalar_tac
  have poolFits : (initializerSeed ty).v128_pool.val.length < Usize.max := by
    simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil]
    scalar_tac
  obtain ⟨⟨status, constantBudget, function⟩, constantCalled, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.constant.total ops law budget (initializerSeed ty) expr ty 0#u32 codeFits poolFits)
  rw [constantCalled, bind_ok]
  simp only [uncurry_apply_pair]
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok unitValue =>
    cases unitValue
    have lowered := (runtime.compiler.initialize.constant.inv ops budget constantBudget
      (initializerSeed ty) function expr ty 0#u32 (.Ok ()) constantCalled).success law
    obtain ⟨code, pool, instruction, frame, appended, certified⟩ := lowered
    have returnFits : function.code.val.length < Usize.max := by
      rw [frame]
      change code.val.length < Usize.max
      rw [appended]
      simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append, List.length_singleton]
      scalar_tac
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with runtime.compiler.initialize.emit.total ops law constantBudget function.code _ returnFits
      as ⟨status, returnBudget, finalCode⟩
    cases status with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with well_formed_total {function with code := finalCode} as ⟨valid⟩
      cases valid with
      | false => simp only [Bool.false_eq_true, ite_false, WP.spec_ok]
      | true =>
        simp only [ite_true]
        step with budget_push ops law returnBudget module.functions {function with code := finalCode} fits
          as ⟨status, afterBudget, functions, changed⟩
        cases status <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]

@[step] theorem _root_.Itasca.runtime.compiler.initialize.expression.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (functionsRequest : module.functions.length + 1 ≤ bound)
    (functionsFit : module.functions.length < Usize.max) :
    runtime.compiler.initialize.expression ops module budget expr ty ⦃ (status, after, afterBudget) =>
      status = .Ok (alloc.vec.Vec.len module.functions) ∧
      afterBudget.instructions.val = budget.instructions.val + 2 ∧ afterBudget.limits = budget.limits ∧
      ∃ function, InitializerCode function expr ty ∧ after.functions.val = module.functions.val ++ [function] ∧
        after = {module with functions := after.functions} ⦄ := by
  unfold runtime.compiler.initialize.expression
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok]
  have codeFits : (initializerSeed ty).code.length < Usize.max := by
    simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, alloc.vec.Vec.length, List.length_nil]
    scalar_tac
  have firstRequest : (initializerSeed ty).code.length + 1 ≤ bound := by
    simpa only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, alloc.vec.Vec.length, List.length_nil, Nat.zero_add]
      using (show 1 ≤ bound by omega)
  have poolReady : ∀ lo hi, expr = .V128 lo hi →
      (initializerSeed ty).v128_pool.length < Usize.max ∧
      (initializerSeed ty).v128_pool.length ≤ U32.max ∧
      (initializerSeed ty).v128_pool.length + 1 ≤ bound := by
    intros lo hi matching
    simp only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, alloc.vec.Vec.length, List.length_nil, Nat.zero_add]
    constructor
    · scalar_tac
    exact ⟨by scalar_tac, by omega⟩
  step with runtime.compiler.initialize.constant.available ops bound available budget (initializerSeed ty) expr ty 0#u32
    (by omega) codeFits firstRequest poolReady
    as ⟨status, charged, function, accepted, usedInstructions, chargedFrame, used, lowered⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have usedCount : charged.instructions.val = budget.instructions.val + 1 := by rw [chargedFrame]; exact used
  have limits : charged.limits = budget.limits := by rw [chargedFrame]
  obtain ⟨code, pool, instruction, same, emitted, constant⟩ := lowered
  have firstCode : function.code.val = [instruction] := by
    rw [same]
    simpa only [initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] using emitted
  have firstLength : function.code.length = 1 := by
    simp only [alloc.vec.Vec.length, firstCode, List.length_singleton]
  step with runtime.compiler.initialize.emit.available ops bound available charged function.code
    (.Return 0#u32 (initializerWidth ty)) (by rw [limits]; omega)
    (by rw [firstLength]; scalar_tac) (by omega)
    as ⟨status, chargedAgain, finalCode, accepted, usedAgain, returnFrame, returnCount, returned⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have shape : InitializerCode {function with code := finalCode} expr ty := by
    refine ⟨⟨instruction, constant.change_code rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [returned, firstCode, List.cons_append, List.nil_append]
    all_goals simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]
  have checked := initializer_well_formed {function with code := finalCode} expr ty shape
    (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]) (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val])
    (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]) (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val])
    (by simp only [same, initializerSeed, alloc.vec.Vec.new, alloc.vec.Vec.from_val]) vector
  step with checked as ⟨valid, validEq⟩
  rw [validEq]
  simp only [ite_true]
  step with budget_push_available ops bound available chargedAgain module.functions
    {function with code := finalCode} functionsFit functionsRequest
    as ⟨status, afterBudget, functions, accepted, sameBudget, appended⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
  refine ⟨rfl, ?_, ?_, _, shape, appended, rfl⟩
  · rw [sameBudget, returnFrame]
    change usedAgain.val = budget.instructions.val + 2
    omega
  · rw [sameBudget, returnFrame, limits]

end Itasca.Runtime.Compiler

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Expression compilation is total with one available retained-function slot.
The bytecode checker is total even when it rejects the synthetic function. -/
@[step] theorem initializer_expression_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr)
    (ty : Itasca.wasm_types.ValueType) (space : initializerSize m + 1 ≤ Usize.max) :
    runtime.compiler.initialize.expression ops m budget expr ty ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 1 ⦄ := by
  have functionsFit : m.functions.length < Usize.max := by
    simp only [initializerSize, alloc.vec.Vec.length] at space ⊢
    omega
  obtain ⟨⟨status, after, afterBudget⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.expression.total ops law m budget expr ty functionsFit)
  rw [called]
  simp only [WP.spec_ok]
  have effect := runtime.compiler.initialize.expression.inv ops m after budget afterBudget expr ty status called
  have growth := effect.growth law
  have frame := effect.frame
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨moduleEq, ?_⟩
  rw [frame]
  simp only [initializerSize]
  omega

end Itasca.Runtime.Compiler
