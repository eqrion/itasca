import Itasca.Runtime.Compiler.Local.Initializer.ConstantContracts
import Itasca.Module.Const.Parser

/-! Segment-emission contracts: exact successful programs, total growth bounds,
and availability from source typing and independent allocation demand. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

inductive ElementProgram (function : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.metadata.Element) : List runtime.bytecode.Instr → Prop where
  | passive (mode : segment.mode = .Passive) : ElementProgram function index segment []
  | declarative (mode : segment.mode = .Declarative) (word : U32) (encoded : word.val = index) :
      ElementProgram function index segment [.ElemDrop word]
  | active (table : U32) (offset : Itasca.wasm_types.ConstExpr)
      (mode : segment.mode = .Active table offset)
      (word length entry : U32) (encoded : word.val = index) (count : length.val = segment.init.length)
      (descriptor : function.indirect.val[entry.val]? = some (word, table))
      (instruction : runtime.bytecode.Instr)
      (constant : ConstantInstruction function 0#u32 offset .I32 instruction) :
      ElementProgram function index segment
        [instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
          .TableInit 0#u32 entry, .ElemDrop word]

inductive DataProgram (function : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.metadata.Data) : List runtime.bytecode.Instr → Prop where
  | passive (mode : segment.mode = .Passive) : DataProgram function index segment []
  | active (memory : U32) (offset : Itasca.wasm_types.ConstExpr)
      (mode : segment.mode = .Active memory offset)
      (word length : U32) (encoded : word.val = index) (count : length.val = segment.init.length)
      (instruction : runtime.bytecode.Instr)
      (constant : ConstantInstruction function 0#u32 offset .I32 instruction) :
      DataProgram function index segment
        [instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
          .MemoryInit 0#u32 word, .DataDrop word]

/-- Successful emission determines the appended instruction without a separate
capacity premise: the actual checked vector append supplies that bound. -/
theorem initializer_emit_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (success : runtime.compiler.initialize.emit ops budget before instruction = .ok (.Ok (), afterBudget, after)) :
    after.val = before.val ++ [instruction] := by
  exact (runtime.compiler.initialize.emit.inv ops budget afterBudget before after instruction (.Ok ()) success).success law


/-- Integer offsets have a single instruction and no literal-pool allocation. -/
theorem initializer_offset_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (expr : Itasca.wasm_types.ConstExpr)
    (offset : (∃ bits, expr = .I32 bits) ∨ (∃ index, expr = .GlobalGet index))
    (success : runtime.compiler.initialize.constant ops budget before expr .I32 0#u32 =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instruction, after = {before with code := after.code} ∧
      after.code.val = before.code.val ++ [instruction] ∧
      ConstantInstruction after 0#u32 expr .I32 instruction := by
  have effect := runtime.compiler.initialize.constant.inv ops budget afterBudget before after expr .I32 0#u32 (.Ok ()) success
  have nonvector : ∀ lo hi, expr ≠ .V128 lo hi := by
    rcases offset with ⟨bits, rfl⟩ | ⟨index, rfl⟩ <;> intros lo hi impossible <;> cases impossible
  have poolEq := effect.pool_of_nonvector nonvector
  obtain ⟨code, pool, instruction, rfl, appended, certified⟩ := effect.success law
  change pool = before.v128_pool at poolEq
  subst pool
  exact ⟨instruction, rfl, appended, certified⟩


theorem valid_offset_shape {env : Itasca.metadata.Env} {expr : Itasca.wasm_types.ConstExpr}
    (valid : Itasca.ModuleConstants.Valid env expr .I32) :
    (∃ bits, expr = .I32 bits) ∨ (∃ index, expr = .GlobalGet index) := by
  cases expr with
  | I32 bits => exact .inl ⟨bits, rfl⟩
  | GlobalGet index => exact .inr ⟨index, rfl⟩
  | I64 _ | F32 _ | F64 _ | V128 _ _ | RefFunc _ => cases valid
  | RefNull ty => cases ty <;> cases valid


/-- Source-typed i32 offsets compile with one instruction and no pool reserve.
The exact field effect is available before any publication checker runs. -/
theorem initializer_offset_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (env : Itasca.metadata.Env) (expr : Itasca.wasm_types.ConstExpr)
    (typed : Itasca.ModuleConstants.Valid env expr .I32)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (capacity : function.code.length < Usize.max) (request : function.code.length + 1 ≤ bound) :
    runtime.compiler.initialize.constant ops budget function expr .I32 0#u32 ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ out.2.2 = {function with code := out.2.2.code} ∧
      ∃ instruction, out.2.2.code.val = function.code.val ++ [instruction] ∧
        ConstantInstruction out.2.2 0#u32 expr .I32 instruction ⦄ := by
  have nonvector : ∀ lo hi, expr ≠ .V128 lo hi := by
    rcases valid_offset_shape typed with ⟨bits, rfl⟩ | ⟨index, rfl⟩ <;>
      intros lo hi impossible <;> cases impossible
  obtain ⟨⟨status, afterBudget, after⟩, called, accepted, used, frame, count, lowered⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.constant.available ops bound available budget function expr .I32 0#u32
      room capacity request (fun lo hi equality => False.elim (nonvector lo hi equality)))
  have effect := runtime.compiler.initialize.constant.inv ops budget afterBudget function after expr .I32 0#u32 status called
  have poolEq := effect.pool_of_nonvector nonvector
  rw [called]
  simp only [WP.spec_ok]
  obtain ⟨code, pool, instruction, rfl, appended, certified⟩ := lowered
  change pool = function.v128_pool at poolEq
  subst pool afterBudget
  exact ⟨accepted, count, rfl, rfl, instruction, appended, certified⟩


@[step] theorem initializer_emit_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (space : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.2.2.val.length ≤ code.val.length + 1 ⦄ := by
  obtain ⟨⟨status, afterBudget, after⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.emit.total ops law budget code instruction space)
  rw [called]
  simp only [WP.spec_ok]
  have growth := (runtime.compiler.initialize.emit.inv ops budget afterBudget code after instruction status called).code law
  rcases growth with unchanged | appended
  · rw [unchanged]
    omega
  · rw [appended, List.length_append, List.length_singleton]


/-- All constant forms return normally, including an allocator or instruction
budget rejection after partial emission. Each vector grows by at most one. -/
@[step] theorem initializer_constant_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (expr : Itasca.wasm_types.ConstExpr)
    (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 1 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  obtain ⟨⟨status, afterBudget, after⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.constant.total ops law budget function expr ty dst codeFits poolFits)
  rw [called]
  simp only [WP.spec_ok]
  have effect := runtime.compiler.initialize.constant.inv ops budget afterBudget function after expr ty dst status called
  have growth := effect.growth law
  refine ⟨growth.1, growth.2, ?_⟩
  have same := congrArg (fun f : runtime.bytecode.CompiledFunction => f.indirect) effect.frame
  exact same


/-- One available instruction emission consumes one unit of instruction budget
and appends its instruction. Bounds are on actual reserve demand. -/
theorem initializer_emit_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (code : alloc.vec.Vec runtime.bytecode.Instr)
    (instruction : runtime.bytecode.Instr)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (fits : code.length < Usize.max) (request : code.length + 1 ≤ bound) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.val = code.val ++ [instruction] ⦄ := by
  apply WP.spec_mono (runtime.compiler.initialize.emit.available ops bound available budget code instruction room fits request)
  rintro ⟨status, afterBudget, after⟩ ⟨accepted, used, rfl, count, appended⟩
  exact ⟨accepted, count, rfl, appended⟩


theorem _root_.Itasca.runtime.compiler.initialize.emit_data.inv {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (valid : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_data ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, DataProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count} ∧
      (instructions = [] ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  unfold runtime.compiler.initialize.emit_data at success
  simp only [runtime.compiler.ExecutableModule.tail.eq,
    Itasca.metadata.Module.impl.tail, bind_ok] at success
  rw [initializer_vec_index _ _ segment found, bind_ok] at success
  cases mode : segment.mode with
  | Passive =>
    simp only [mode] at success
    have output := Result.ok_injective success
    have same := congrArg (fun out => out.2.2) output
    dsimp only at same
    subst after
    exact ⟨[], .passive mode, by simp, rfl, .inl ⟨rfl, rfl⟩⟩
  | Active memory offset =>
    simp only [mode] at success
    obtain ⟨⟨result, b1, first⟩, constant, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      obtain ⟨instruction, firstFields, firstCode, firstInstruction⟩ :=
        initializer_offset_success ops law budget b1 {before with slot_count := 3#u32} first offset
          (valid_offset_shape (valid memory offset mode)) constant
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b2, second⟩, emit1, rest⟩ := initializer_bind_success rest
      cases result with
      | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unitValue =>
        cases unitValue
        have code1 := initializer_emit_success ops law b1 b2 first.code second _ emit1
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨result, boundedLen, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok length =>
          have countSpec := bounded_index (alloc.vec.Vec.len segment.init)
          rw [boundedLen, WP.spec_ok] at countSpec
          have count := countSpec length rfl
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨result, b3, third⟩, emit2, rest⟩ := initializer_bind_success rest
          cases result with
          | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unitValue =>
            cases unitValue
            have code2 := initializer_emit_success ops law b2 b3 second third _ emit2
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
            obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok word =>
              have indexSpec := bounded_index index
              rw [boundedIndex, WP.spec_ok] at indexSpec
              have encoded := indexSpec word rfl
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
              obtain ⟨⟨result, b4, fourth⟩, emit3, rest⟩ := initializer_bind_success rest
              cases result with
              | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
              | Ok unitValue =>
                cases unitValue
                have code3 := initializer_emit_success ops law b3 b4 third fourth _ emit3
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                obtain ⟨⟨result, b5, fifth⟩, emit4, rest⟩ := initializer_bind_success rest
                cases result with
                | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                | Ok unitValue =>
                  cases unitValue
                  have code4 := initializer_emit_success ops law b4 b5 fourth fifth _ emit4
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                  have output := Result.ok_injective rest
                  have fields := congrArg (fun out => out.2.2) output
                  dsimp only at fields
                  subst after
                  refine ⟨[instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
                    .MemoryInit 0#u32 word, .DataDrop word], ?_, ?_, ?_, ?_⟩
                  · exact .active memory offset mode word length encoded count instruction (firstInstruction.change_code rfl)
                  · simp [code4, code3, code2, code1, firstCode, List.append_assoc]
                  · rw [firstFields]
                  · exact .inr ⟨rfl, by rw [firstFields]⟩


theorem _root_.Itasca.runtime.compiler.initialize.emit_element.inv {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Element)
    (found : module.module.env.elements.val[index.val]? = some segment)
    (valid : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_element ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, ElementProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count, indirect := after.indirect} ∧
      after.indirect.val.take before.indirect.length = before.indirect.val ∧
      (instructions.length ≤ 1 ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  unfold runtime.compiler.initialize.emit_element at success
  simp only [runtime.compiler.ExecutableModule.env.eq,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok] at success
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok] at success
  cases mode : segment.mode with
  | Passive =>
    simp only [mode] at success
    have output := Result.ok_injective success
    have same := congrArg (fun out => out.2.2) output
    dsimp only at same
    subst after
    exact ⟨[], .passive mode, by simp, rfl, by simp, .inl ⟨by simp, rfl⟩⟩
  | Declarative =>
    simp only [mode] at success
    obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok word =>
      have indexSpec := bounded_index index
      rw [boundedIndex, WP.spec_ok] at indexSpec
      have encoded := indexSpec word rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b1, instructions⟩, emitted, rest⟩ := initializer_bind_success rest
      have output := Result.ok_injective rest
      have resultEq := congrArg Prod.fst output
      dsimp only at resultEq
      subst result
      have fields := congrArg (fun out => out.2.2) output
      dsimp only at fields
      subst after
      have code := initializer_emit_success ops law budget b1 before.code instructions _ emitted
      exact ⟨[.ElemDrop word], .declarative mode word encoded, code, rfl, by simp, .inl ⟨by simp, rfl⟩⟩
  | Active table offset =>
    simp only [mode] at success
    obtain ⟨⟨result, b1, first⟩, constant, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      obtain ⟨instruction, firstFields, firstCode, firstInstruction⟩ :=
        initializer_offset_success ops law budget b1 {before with slot_count := 3#u32} first offset
          (valid_offset_shape (valid table offset mode)) constant
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b2, second⟩, emit1, rest⟩ := initializer_bind_success rest
      cases result with
      | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unitValue =>
        cases unitValue
        have code1 := initializer_emit_success ops law b1 b2 first.code second _ emit1
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨result, boundedLen, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok length =>
          have countSpec := bounded_index (alloc.vec.Vec.len segment.init)
          rw [boundedLen, WP.spec_ok] at countSpec
          have count := countSpec length rfl
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨result, b3, third⟩, emit2, rest⟩ := initializer_bind_success rest
          cases result with
          | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unitValue =>
            cases unitValue
            have code2 := initializer_emit_success ops law b2 b3 second third _ emit2
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
            obtain ⟨result, boundedEntry, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok entry =>
              have entrySpec := bounded_index (alloc.vec.Vec.len first.indirect)
              rw [boundedEntry, WP.spec_ok] at entrySpec
              have entryEncoded := entrySpec entry rfl
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
              obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success rest
              cases result with
              | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
              | Ok word =>
                have indexSpec := bounded_index index
                rw [boundedIndex, WP.spec_ok] at indexSpec
                have encoded := indexSpec word rfl
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                obtain ⟨⟨result, b4, indirect⟩, pushed, rest⟩ := initializer_bind_success rest
                cases result with
                | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                | Ok unitValue =>
                  cases unitValue
                  have indirectValues := (budget_push_success ops law b3 b4 first.indirect indirect (word, table) pushed).2
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                  obtain ⟨⟨result, b5, fourth⟩, emit3, rest⟩ := initializer_bind_success rest
                  cases result with
                  | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                  | Ok unitValue =>
                    cases unitValue
                    have code3 := initializer_emit_success ops law b4 b5 third fourth _ emit3
                    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                    obtain ⟨⟨result, b6, fifth⟩, emit4, rest⟩ := initializer_bind_success rest
                    cases result with
                    | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                    | Ok unitValue =>
                      cases unitValue
                      have code4 := initializer_emit_success ops law b5 b6 fourth fifth _ emit4
                      have output := Result.ok_injective rest
                      have fields := congrArg (fun out => out.2.2) output
                      dsimp only at fields
                      subst after
                      refine ⟨[instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
                        .TableInit 0#u32 entry, .ElemDrop word], ?_, ?_, ?_, ?_, ?_⟩
                      · exact .active table offset mode word length entry encoded count
                          (by simp [indirectValues, entryEncoded]) instruction (firstInstruction.change_code rfl)
                      · simp [code4, code3, code2, code1, firstCode, List.append_assoc]
                      · rw [firstFields]
                      · have same := congrArg runtime.bytecode.CompiledFunction.indirect firstFields
                        dsimp only at same
                        simp [indirectValues, same]
                      · exact .inr ⟨rfl, by rw [firstFields]⟩


theorem _root_.Itasca.runtime.compiler.initialize.emit_data.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_data ops m budget function index ⦃ (status, afterBudget, after) =>
      after.code.val.length ≤ function.code.val.length + 5 ∧
      after.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      after.indirect = function.indirect ⦄ := by
  unfold runtime.compiler.initialize.emit_data
  simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok]
  step
  repeat' first
    | (refine WP.spec_bind (initializer_constant_total ops law _ _ _ _ _ ?_ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextFunction⟩ ⟨code, pool, pairs⟩
            dsimp only at code pool pairs
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (initializer_emit_total ops law _ _ _ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextVector⟩ growth
            dsimp only at growth
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (bounded_index _) ?_
       rintro status encoded
       cases status)
    | simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
    | split
    | (apply WP.spec.ret
       try dsimp only
       repeat' apply And.intro
       all_goals first | assumption | rfl | scalar_tac)


theorem _root_.Itasca.runtime.compiler.initialize.emit_element.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.env.elements.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max)
    (pairFits : function.indirect.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_element ops m budget function index ⦃ (status, afterBudget, after) =>
      after.code.val.length ≤ function.code.val.length + 5 ∧
      after.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      after.indirect.val.length ≤ function.indirect.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.emit_element
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
  step
  · simpa [alloc.vec.Vec.deref] using bound
  repeat' first
    | (refine WP.spec_bind (initializer_constant_total ops law _ _ _ _ _ ?_ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextFunction⟩ ⟨code, pool, pairs⟩
            dsimp only at code pool pairs
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (initializer_emit_total ops law _ _ _ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextVector⟩ growth
            dsimp only at growth
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (initializer_push_total ops law _ _ _ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextVector⟩ growth
            dsimp only at growth
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (bounded_index _) ?_
       rintro status encoded
       cases status)
    | simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
    | split
    | (apply WP.spec.ret
       try dsimp only
       repeat' apply And.intro
       all_goals first | assumption | rfl | scalar_tac)


structure DataEmissionDemand {A : Type} (bound : Nat)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Data) : Prop where
  lookup : module.module.tail.data.val[index.val]? = some segment
  typed : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32
  instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val
  capacity : function.code.length + 5 ≤ Usize.max
  request : function.code.length + 5 ≤ bound
  indexBound : index.val ≤ U32.max
  lengthBound : segment.init.length ≤ U32.max

theorem _root_.Itasca.runtime.compiler.initialize.emit_data.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Data)
    (demand : DataEmissionDemand bound module budget function index segment) :
    runtime.compiler.initialize.emit_data ops module budget function index ⦃ (status, afterBudget, after) =>
      status = .Ok () ∧ afterBudget.instructions.val ≤ budget.instructions.val + 5 ∧
      afterBudget.limits = budget.limits ∧ after.code.length ≤ function.code.length + 5 ∧
      after.v128_pool = function.v128_pool ∧ after.indirect = function.indirect ⦄ := by
  obtain ⟨lookup, typed, instructions, capacity, request, indexBound, lengthBound⟩ := demand
  unfold runtime.compiler.initialize.emit_data
  simp only [runtime.compiler.ExecutableModule.tail.eq,Itasca.metadata.Module.impl.tail,bind_ok]
  rw [initializer_vec_index _ _ segment lookup,bind_ok]
  cases mode : segment.mode with
  | Passive =>
    simp only [mode,WP.spec_ok]
    exact ⟨rfl,by omega,rfl,by omega,rfl,rfl⟩
  | Active memory offset =>
    simp only [mode]
    step with initializer_offset_available ops bound available budget {function with slot_count := 3#u32}
      module.module.env offset (typed memory offset mode) (by omega)
      (by change function.code.length < Usize.max; omega)
      (by change function.code.length+1 ≤ bound; omega)
      as ⟨status,b1,first,accepted,used1,limits1,fields,instruction,code1,constant⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have firstLength : first.code.length = function.code.length + 1 := by
      simp only [alloc.vec.Vec.length,code1,List.length_append,List.length_singleton]
    step with initializer_emit_available ops bound available b1 first.code (.Const32 1#u32 0#u32)
      (by rw [limits1]; omega) (by omega) (by omega)
      as ⟨status,b2,second,accepted,used2,limits2,code2⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available (alloc.vec.Vec.len segment.init) lengthBound
      as ⟨status,length,accepted,encodedLength⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have secondLength : second.length = function.code.length + 2 := by
      simp only [alloc.vec.Vec.length,code2,List.length_append,List.length_singleton] at firstLength ⊢
      omega
    step with initializer_emit_available ops bound available b2 second (.Const32 2#u32 length)
      (by rw [limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b3,third,accepted,used3,limits3,code3⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have thirdLength : third.length = function.code.length + 3 := by
      simp only [alloc.vec.Vec.length,code3,List.length_append,List.length_singleton] at secondLength ⊢
      omega
    step with initializer_emit_available ops bound available b3 third (.MemoryInit 0#u32 word)
      (by rw [limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b4,fourth,accepted,used4,limits4,code4⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have fourthLength : fourth.length = function.code.length + 4 := by
      simp only [alloc.vec.Vec.length,code4,List.length_append,List.length_singleton] at thirdLength ⊢
      omega
    step with initializer_emit_available ops bound available b4 fourth (.DataDrop word)
      (by rw [limits4,limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b5,fifth,accepted,used5,limits5,code5⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    refine ⟨rfl,?_,?_,?_,?_,?_⟩
    · omega
    · exact limits5.trans (limits4.trans (limits3.trans (limits2.trans limits1)))
    · simp only [alloc.vec.Vec.length,code5,List.length_append,List.length_singleton]
      simp only [alloc.vec.Vec.length] at fourthLength capacity
      omega
    · exact congrArg (fun value => value.v128_pool) fields
    · exact congrArg (fun value => value.indirect) fields


structure ElementEmissionDemand {A : Type} (bound : Nat)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Element) : Prop where
  lookup : module.module.env.elements.val[index.val]? = some segment
  typed : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32
  instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val
  capacity : function.code.length + 5 ≤ Usize.max
  request : function.code.length + 5 ≤ bound
  indexBound : index.val ≤ U32.max
  lengthBound : segment.init.length ≤ U32.max
  pairIndex : function.indirect.length ≤ U32.max
  pairCapacity : function.indirect.length < Usize.max
  pairReserve : function.indirect.length + 1 ≤ bound

theorem _root_.Itasca.runtime.compiler.initialize.emit_element.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Element)
    (demand : ElementEmissionDemand bound module budget function index segment) :
    runtime.compiler.initialize.emit_element ops module budget function index ⦃ (status, afterBudget, after) =>
      status = .Ok () ∧ afterBudget.instructions.val ≤ budget.instructions.val + 5 ∧
      afterBudget.limits = budget.limits ∧ after.code.length ≤ function.code.length + 5 ∧
      after.v128_pool = function.v128_pool ∧ after.indirect.length ≤ function.indirect.length + 1 ⦄ := by
  obtain ⟨lookup, typed, instructions, capacity, request, indexBound, lengthBound, pairIndex, pairCapacity, pairReserve⟩ := demand
  unfold runtime.compiler.initialize.emit_element
  simp only [runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements,bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using lookup),bind_ok]
  cases mode : segment.mode with
  | Passive =>
    simp only [mode,WP.spec_ok]
    exact ⟨rfl,by omega,rfl,by omega,rfl,by omega⟩
  | Declarative =>
    simp only [mode]
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with initializer_emit_available ops bound available budget function.code (.ElemDrop word)
      (by omega) (by omega) (by omega)
      as ⟨status,charged,code,accepted,used,limits,appended⟩
    refine ⟨accepted,by omega,limits,?_,?_⟩
    · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
      omega
    · omega
  | Active table offset =>
    simp only [mode]
    step with initializer_offset_available ops bound available budget {function with slot_count := 3#u32}
      module.module.env offset (typed table offset mode) (by omega)
      (by change function.code.length < Usize.max; omega)
      (by change function.code.length+1 ≤ bound; omega)
      as ⟨status,b1,first,accepted,used1,limits1,fields,instruction,code1,constant⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have firstLength : first.code.length = function.code.length + 1 := by
      simp only [alloc.vec.Vec.length,code1,List.length_append,List.length_singleton]
    step with initializer_emit_available ops bound available b1 first.code (.Const32 1#u32 0#u32)
      (by rw [limits1]; omega) (by omega) (by omega)
      as ⟨status,b2,second,accepted,used2,limits2,code2⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available (alloc.vec.Vec.len segment.init) lengthBound
      as ⟨status,length,accepted,encodedLength⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have secondLength : second.length = function.code.length + 2 := by
      simp only [alloc.vec.Vec.length,code2,List.length_append,List.length_singleton] at firstLength ⊢
      omega
    step with initializer_emit_available ops bound available b2 second (.Const32 2#u32 length)
      (by rw [limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b3,third,accepted,used3,limits3,code3⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have firstPairs : first.indirect = function.indirect := congrArg (fun value => value.indirect) fields
    step with bounded_index_available (alloc.vec.Vec.len first.indirect) (by simpa [firstPairs] using pairIndex)
      as ⟨status,entry,accepted,entryEq⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have thirdLength : third.length = function.code.length + 3 := by
      simp only [alloc.vec.Vec.length,code3,List.length_append,List.length_singleton] at secondLength ⊢
      omega
    step with budget_push_available ops bound available b3 first.indirect (word,table)
      (by simpa [firstPairs] using pairCapacity) (by simpa [firstPairs] using pairReserve)
      as ⟨status,pairBudget,pairs,accepted,sameBudget,appendedPairs⟩
    subst status pairBudget
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with initializer_emit_available ops bound available b3 third (.TableInit 0#u32 entry)
      (by rw [limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b4,fourth,accepted,used4,limits4,code4⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have fourthLength : fourth.length = function.code.length + 4 := by
      simp only [alloc.vec.Vec.length,code4,List.length_append,List.length_singleton] at thirdLength ⊢
      omega
    step with initializer_emit_available ops bound available b4 fourth (.ElemDrop word)
      (by rw [limits4,limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b5,fifth,accepted,used5,limits5,code5⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    refine ⟨trivial,?_,?_,?_,?_,?_⟩
    · omega
    · exact limits5.trans (limits4.trans (limits3.trans (limits2.trans limits1)))
    · simp only [alloc.vec.Vec.length,code5,List.length_append,List.length_singleton]
      simp only [alloc.vec.Vec.length] at fourthLength capacity
      omega
    · exact congrArg (fun value => value.v128_pool) fields
    · simp only [alloc.vec.Vec.length,appendedPairs,List.length_append,List.length_singleton]
      simp [firstPairs]


end Itasca.Runtime.Compiler
