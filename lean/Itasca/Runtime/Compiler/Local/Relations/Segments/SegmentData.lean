import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: SegmentProgram, SegmentEmit, SegmentData.
-/

/-! ## SegmentProgram -/

section

/-! Syntactic programs emitted for active and declarative segments. The
certificate records source segment indices and actual embedded descriptor
lookups; runtime bounds and source typing remain separate obligations. -/
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

/-- The initialization function is the source-ordered concatenation of segment
programs followed by a zero-result return. -/
structure SegmentProgramBody (module : runtime.compiler.ExecutableModule)
    (function : runtime.bytecode.CompiledFunction)
    (elementPrograms dataPrograms : List (List runtime.bytecode.Instr)) : Prop where
  elementCount : elementPrograms.length = module.module.env.elements.length
  dataCount : dataPrograms.length = module.module.tail.data.length
  elements : ∀ index segment, module.module.env.elements.val[index]? = some segment →
    ∃ instructions, elementPrograms[index]? = some instructions ∧ ElementProgram function index segment instructions
  datas : ∀ index segment, module.module.tail.data.val[index]? = some segment →
    ∃ instructions, dataPrograms[index]? = some instructions ∧ DataProgram function index segment instructions
  instructions : function.code.val = elementPrograms.flatten ++ dataPrograms.flatten ++ [.Return 0#u32 0#u32]
  capacity : function.slot_count = 0#u32 ∨ function.slot_count = 3#u32
  activeCapacity : (∃ (index : Nat) (instructions : List runtime.bytecode.Instr), elementPrograms[index]? = some instructions ∧ instructions.length = 5) ∨
    (∃ (index : Nat) (instructions : List runtime.bytecode.Instr), dataPrograms[index]? = some instructions ∧ instructions.length = 5) →
    function.slot_count = 3#u32
  localSlots : function.local_slots = 0#u32
  paramSlots : function.param_slots = 0#u32
  locals : function.locals.val = []

def SegmentProgram (module : runtime.compiler.ExecutableModule) (function : runtime.bytecode.CompiledFunction) : Prop :=
  ∃ elements datas, SegmentProgramBody module function elements datas

end Itasca.Runtime.Compiler

end

/-! ## SegmentEmit -/

section

/-!
Successful emission determines the appended instruction without a separate capacity premise: the actual checked vector append supplies that bound.

Main declarations: `initializer_emit_success` and `initializer_offset_success`. A direct consumer is `Compiler.Local.Relations.Segments.SegmentData`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Successful emission determines the appended instruction without a separate
capacity premise: the actual checked vector append supplies that bound. -/
theorem initializer_emit_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (success : runtime.compiler.initialize.emit ops budget before instruction = .ok (.Ok (), afterBudget, after)) :
    after.val = before.val ++ [instruction] := by
  unfold runtime.compiler.initialize.emit at success
  obtain ⟨⟨result, charged⟩, charge, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    exact (budget_push_success ops law charged afterBudget before after instruction rest).2

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
  rcases offset with ⟨bits, rfl⟩ | ⟨index, rfl⟩
  all_goals
    simp only [runtime.compiler.initialize.constant, lift, bind_ok] at success
    obtain ⟨⟨result, charged, instructions⟩, emitted, rest⟩ := initializer_bind_success success
    have output := Result.ok_injective rest
    have resultEq := congrArg Prod.fst output
    dsimp only at resultEq
    subst result
    have fields := congrArg (fun out => out.2.2) output
    dsimp only at fields
    subst after
    have values := initializer_emit_success ops law budget charged before.code instructions _ emitted
    refine ⟨_, rfl, values, ?_⟩
    first | exact .i32 _ _ | exact .global _ _ (by intro h; cases h)

end Itasca.Runtime.Compiler

end

/-! ## SegmentData -/

section

/-!
Validated data offsets and emitted data-initializer programs.

Main declarations: `valid_offset_shape` and `emit_data_program`. A direct consumer is `Compiler.Local.Relations.Segments.SegmentFinish`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem valid_offset_shape {env : Itasca.metadata.Env} {expr : Itasca.wasm_types.ConstExpr}
    (valid : Itasca.ModuleConstants.Valid env expr .I32) :
    (∃ bits, expr = .I32 bits) ∨ (∃ index, expr = .GlobalGet index) := by
  cases expr with
  | I32 bits => exact .inl ⟨bits, rfl⟩
  | GlobalGet index => exact .inr ⟨index, rfl⟩
  | I64 _ | F32 _ | F64 _ | V128 _ _ | RefFunc _ => cases valid
  | RefNull ty => cases ty <;> cases valid

theorem emit_data_program {A : Type} (ops : runtime.platform.Alloc A)
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

end Itasca.Runtime.Compiler

end
