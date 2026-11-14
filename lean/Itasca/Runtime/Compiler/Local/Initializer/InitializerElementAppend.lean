import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Module.Const.Parser

/-!
Sections, each formerly its own module: InitializerProofs, InitializerExpression, InitializerMappings, InitializerMappingLoops, InitializerElementAppend.
-/

/-! ## InitializerProofs -/

section

/-! The extracted synthetic-initializer emitter and constant compiler terminate
under allocator laws and representable vector lengths. Successful calls append
exactly the certified scalar/reference/vector instruction, with vector constants
embedded in the actual pool. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem initializer_emit {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (fits : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.1 = .Ok () → out.2.2.val = code.val ++ [instruction] ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction ops budget as ⟨result, charged, limits, count⟩
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_mono (budget_push ops law charged code instruction fits)
    rintro ⟨result, b, v⟩ hp success
    rcases hp with ⟨rfl, hb, hv⟩ | ⟨rfl, hv, he⟩
    · exact hv
    · cases success

@[step] theorem bounded_index (value : Usize) :
    runtime.compiler.bounded_index value ⦃ result =>
      ∀ word, result = .Ok word → word.val = value.val ⦄ := by
  unfold runtime.compiler.bounded_index
  step
  split
  · simp
  · step as ⟨word, hword⟩
    intro w equality
    cases equality
    simp only [hword, UScalar.cast_val_eq]
    simp_all [core.num.U32.MAX, U32.rMax]
    scalar_tac

def ConstantLowered (before after : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32) : Prop :=
  ∃ code pool instruction,
    after = { before with code, v128_pool := pool } ∧
    code.val = before.code.val ++ [instruction] ∧ ConstantInstruction after dst expr ty instruction

@[step] theorem initializer_constant {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.1 = .Ok () → ConstantLowered function out.2.2 expr ty dst ⦄ := by
  cases expr with
  | I32 value =>
    unfold runtime.compiler.initialize.constant
    step as ⟨bits, hbits⟩
    subst bits
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.i32 value ty⟩
  | I64 value =>
    unfold runtime.compiler.initialize.constant
    step as ⟨bits, hbits⟩
    subst bits
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.i64 value ty⟩
  | F32 value =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.f32 value ty⟩
  | F64 value =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.f64 value ty⟩
  | RefNull elem =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.refNull ty elem⟩
  | RefFunc index =>
    unfold runtime.compiler.initialize.constant
    step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
    intro success
    exact ⟨code, function.v128_pool, _, rfl, hc success, ConstantInstruction.refFunc ty index⟩
  | GlobalGet index =>
    cases ty <;> unfold runtime.compiler.initialize.constant <;> simp only [bind_ok]
    all_goals
      step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
      intro success
      refine ⟨code, function.v128_pool, _, rfl, hc success, ?_⟩
      first | exact ConstantInstruction.globalVector index | exact ConstantInstruction.global _ index (by intro h; cases h)
  | V128 lo hi =>
    unfold runtime.compiler.initialize.constant
    step with bounded_index (alloc.vec.Vec.len function.v128_pool) as ⟨result, hp⟩
    cases result with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pool =>
      have poolIndex := hp pool rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨low, hlow⟩
      subst low
      step as ⟨high, hhigh⟩
      subst high
      step as ⟨shifted, hshifted, hshiftbv⟩
      step as ⟨word, hword, hwordbv⟩
      step with budget_push ops law budget function.v128_pool word poolFits as ⟨result, b, values, hv⟩
      rcases hv with ⟨hr, hb, hv⟩ | ⟨hr, hv, he⟩
      · subst result b
        simp only [bind_ok]
        step with initializer_emit ops law budget function.code _ codeFits as ⟨result, b, code, hc⟩
        intro success
        refine ⟨code, values, _, rfl, hc success, ConstantInstruction.v128 lo hi ty pool ?_⟩
        have packed : word = initializerBits lo hi := by
          apply U128.bv_eq_imp_eq
          exact hwordbv.trans (congrArg (fun bits => (UScalar.cast .U128 lo).bv ||| bits) hshiftbv)
        simp [hv, poolIndex, alloc.vec.Vec.len, packed]
      · subst result values
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
end Itasca.Runtime.Compiler

end

/-! ## InitializerExpression -/

section

/-! Successful synthetic initializer compilation retains its exact two-instruction
program, literal pool, slot width, and position in the executable module. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std


def initializerSeed (ty : Itasca.wasm_types.ValueType) : runtime.bytecode.CompiledFunction :=
  { locals := alloc.vec.Vec.new _, local_slots := 0#u32, param_slots := 0#u32,
    slot_count := initializerWidth ty, max_stack := 0#usize, code := alloc.vec.Vec.new _,
    jump_tables := alloc.vec.Vec.new _, v128_pool := alloc.vec.Vec.new _,
    indirect := alloc.vec.Vec.new _, simd := alloc.vec.Vec.new _, source_offsets := alloc.vec.Vec.new _,
    controls := alloc.vec.Vec.new _, type_index := 0#u32, body_start := 0#usize, body_end := 0#usize }

theorem initializer_synthetic (ty : Itasca.wasm_types.ValueType) :
    runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) (initializerWidth ty) =
      .ok (initializerSeed ty) := rfl

/-- Actual successful expression lowering supplies the executable initializer certificate.
Source expression typing and runtime index resolution are separate obligations. -/
theorem initializer_expression {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (index : Usize) (after : runtime.compiler.ExecutableModule) (budgetAfter : runtime.compiler.Budget A)
    (success : runtime.compiler.initialize.expression ops module budget expr ty =
      .ok (.Ok index, after, budgetAfter)) :
    ∃ function, InitializerCode function expr ty ∧ index.val = module.functions.val.length ∧
      after = { module with functions := after.functions } ∧
      after.functions.val = module.functions.val ++ [function] := by
  unfold runtime.compiler.initialize.expression at success
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok] at success
  have emptyFits : (initializerSeed ty).code.val.length < Usize.max := by
    simp [initializerSeed]
    scalar_tac
  have poolFits : (initializerSeed ty).v128_pool.val.length < Usize.max := by
    simp [initializerSeed]
    scalar_tac
  obtain ⟨⟨result, b1, function⟩, hconstant, hconstantPost⟩ :=
    WP.spec_imp_exists (initializer_constant ops law budget (initializerSeed ty) expr ty 0#u32 emptyFits poolFits)
  rw [hconstant, bind_ok] at success
  simp only [uncurry_apply_pair] at success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
  | Ok value =>
    cases value
    have lowered : ConstantLowered (initializerSeed ty) function expr ty 0#u32 := hconstantPost rfl
    obtain ⟨code, pool, instruction, hfunction, hcode, relation⟩ := lowered
    have codeFits : function.code.val.length < Usize.max := by
      rw [hfunction]
      change code.val.length < Usize.max
      rw [hcode]
      simp [initializerSeed]
      scalar_tac
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at success
    obtain ⟨⟨result, b2, finalCode⟩, hemit, hemitPost⟩ := WP.spec_imp_exists
      (initializer_emit ops law b1 function.code (.Return 0#u32 (initializerWidth ty)) codeFits)
    rw [hemit, bind_ok] at success
    simp only [uncurry_apply_pair] at success
    cases result with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
    | Ok value =>
      cases value
      have appended := hemitPost rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at success
      cases checked : runtime.bytecode.CompiledFunction.well_formed { function with code := finalCode } with
      | ret valid =>
        rw [checked, bind_ok] at success
        cases valid with
        | false => simp at success
        | true =>
          simp only [↓reduceIte] at success
          cases hpush : runtime.compiler.Budget.push ops b2 module.functions
              { function with code := finalCode } with
          | ret output =>
            rcases output with ⟨result, b3, functions⟩
            rw [hpush, bind_ok] at success
            simp only [uncurry_apply_pair] at success
            cases result with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at success
            | Ok value =>
              cases value
              obtain ⟨hb, hfunctions⟩ := budget_push_success ops law b2 b3 module.functions functions
                { function with code := finalCode } hpush
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at success
              have output := Result.ok_injective success
              have hindex := congrArg Prod.fst output
              have hafter := congrArg (fun out => out.2.1) output
              have indexEq := core.result.Result.Ok.inj hindex
              change { module with functions := functions } = after at hafter
              subst after
              refine ⟨{ function with code := finalCode }, ?_, ?_, rfl, hfunctions⟩
              · refine ⟨⟨instruction, relation.change_code rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
                · rw [appended, hfunction]
                  simp [hcode, initializerSeed]
                all_goals simp [hfunction, initializerSeed]
              · simpa [alloc.vec.Vec.len] using congrArg UScalar.val indexEq.symm
          | vis effect continuation =>
            rw [hpush, bind_vis] at success
            exact (vis_not_ok success).elim
          | div =>
            rw [hpush, bind_div] at success
            exact (div_not_ok success).elim
      | vis effect continuation =>
        rw [checked, bind_vis] at success
        exact (vis_not_ok success).elim
      | div =>
        rw [checked, bind_div] at success
        exact (div_not_ok success).elim
end Itasca.Runtime.Compiler

end

/-! ## InitializerMappings -/

section

/-! Exact retained initializer indices from the actual compiler helpers. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem initializer_slice_index {T : Type} (values : Slice T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) : Slice.index_usize values index = .ok value := by
  have bound : index.val < values.length := (List.getElem?_eq_some_iff.mp found).1
  have spec : Slice.index_usize values index ⦃ out => out = value ⦄ := by
    step as ⟨out, hout⟩
    have read := List.getElem?_eq_getElem bound
    rw [found] at read
    exact hout.trans (Option.some.inj read).symm
  obtain ⟨out, call, rfl⟩ := WP.spec_imp_exists spec
  exact call

/-- A successful global initializer append records the exact source expression,
new function index, and two-instruction certificate, preserving other fields. -/
theorem initializer_lower_global {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (global : Itasca.metadata.Global)
    (found : module.module.env.globals.val[index.val]? = some global)
    (success : runtime.compiler.initialize.lower_global ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ function fnIndex,
      InitializerCode function global.init global.gtype.valtype ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions, global_initializers := after.global_initializers } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      after.global_initializers.val = module.global_initializers.val ++ [fnIndex] := by
  unfold runtime.compiler.initialize.lower_global at success
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok] at success
  rw [initializer_slice_index _ _ global (by simpa [alloc.vec.Vec.deref] using found), bind_ok] at success
  obtain ⟨⟨result, middle, b1⟩, expression, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok fnIndex =>
    obtain ⟨function, certificate, position, changed, appended⟩ :=
      initializer_expression ops law module budget global.init global.gtype.valtype fnIndex middle b1 expression
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨result, b2, indices⟩, pushed, rest⟩ := initializer_bind_success rest
    have output := Result.ok_injective rest
    have sameResult := congrArg Prod.fst output
    dsimp only at sameResult
    subst result
    have fields := congrArg (fun out => out.2.1) output
    dsimp only at fields
    subst after
    obtain ⟨_, pushedValues⟩ := budget_push_success ops law b1 b2 middle.global_initializers indices fnIndex pushed
    refine ⟨function, fnIndex, certificate, position, ?_, appended, ?_⟩
    · rw [changed]
    · have same := congrArg runtime.compiler.ExecutableModule.global_initializers changed
      change middle.global_initializers = module.global_initializers at same
      simpa only [same] using pushedValues

def InitializerAt (functions : List runtime.bytecode.CompiledFunction)
    (index : Usize) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) : Prop :=
  ∃ code, functions[index.val]? = some code ∧ InitializerCode code expr ty

theorem InitializerAt.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {index expr ty}
    (cert : InitializerAt before index expr ty) : InitializerAt after index expr ty := by
  obtain ⟨code, found, compiled⟩ := cert
  have bound := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨code, ?_, compiled⟩
  rw [← prefixEq, List.getElem?_take] at found
  simpa [bound] using found

theorem initializer_vec_index {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) values index = .ok value :=
  initializer_slice_index values.slice index value found

/-- Each successful element-value lowering appends the actual source value's
initializer and records precisely its issued function index. -/
theorem initializer_lower_element_value {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (success : runtime.compiler.initialize.lower_element_value ops module budget indices i j =
      .ok (.Ok (), after, budgetAfter, outIndices)) :
    ∃ function fnIndex,
      InitializerCode function expr (Itasca.ModuleConstants.referenceValueType segment.elem) ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      outIndices.val = indices.val ++ [fnIndex] := by
  unfold runtime.compiler.initialize.lower_element_value at success
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok] at success
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok,
    initializer_vec_index _ _ expr valueFound, bind_ok] at success
  simp only [bind_ok] at success
  have elemType : wasm_types.ElemType.value_type segment.elem =
      .ok (Itasca.ModuleConstants.referenceValueType segment.elem) := by
    cases segment.elem <;> rfl
  rw [elemType, bind_ok] at success
  obtain ⟨⟨result, middle, b1⟩, expression, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok fnIndex =>
    obtain ⟨function, certificate, position, changed, appended⟩ :=
      initializer_expression ops law module budget expr _ fnIndex middle b1 expression
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨result, b2, outputIndices⟩, pushed, rest⟩ := initializer_bind_success rest
    have output := Result.ok_injective rest
    have sameResult := congrArg Prod.fst output
    dsimp only at sameResult
    subst result
    have fields := congrArg (fun out => out.2.1) output
    have sameIndices := congrArg (fun out => out.2.2.2) output
    dsimp only at fields sameIndices
    subst after outIndices
    obtain ⟨_, pushedValues⟩ := budget_push_success ops law b1 b2 indices outputIndices fnIndex pushed
    exact ⟨function, fnIndex, certificate, position, changed, appended, pushedValues⟩

theorem initializer_lower_data_active {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Data)
    (memory : U32) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (active : segment.mode = .Active memory expr)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ function fnIndex,
      InitializerCode function expr .I32 ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions, data_offsets := after.data_offsets } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      after.data_offsets.val = module.data_offsets.val ++ [some fnIndex] := by
  unfold runtime.compiler.initialize.lower_data_offset at success
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.metadata.Module.impl.tail, bind_ok] at success
  rw [initializer_vec_index _ _ segment found, bind_ok, active] at success
  obtain ⟨⟨result, middle, b1⟩, expression, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok fnIndex =>
    obtain ⟨function, certificate, position, changed, appended⟩ :=
      initializer_expression ops law module budget expr .I32 fnIndex middle b1 expression
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨result, b2, indices⟩, pushed, rest⟩ := initializer_bind_success rest
    have output := Result.ok_injective rest
    have sameResult := congrArg Prod.fst output
    dsimp only at sameResult
    subst result
    have fields := congrArg (fun out => out.2.1) output
    dsimp only at fields
    subst after
    obtain ⟨_, pushedValues⟩ := budget_push_success ops law b1 b2 middle.data_offsets indices (some fnIndex) pushed
    refine ⟨function, fnIndex, certificate, position, ?_, appended, ?_⟩
    · rw [changed]
    · have same := congrArg runtime.compiler.ExecutableModule.data_offsets changed
      change middle.data_offsets = module.data_offsets at same
      simpa only [same] using pushedValues

/-- Passive data segments retain an explicit absent offset without adding code. -/
theorem initializer_lower_data_passive {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (passive : segment.mode = .Passive)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    after = { module with data_offsets := after.data_offsets } ∧
      after.data_offsets.val = module.data_offsets.val ++ [none] := by
  unfold runtime.compiler.initialize.lower_data_offset at success
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.metadata.Module.impl.tail, bind_ok] at success
  rw [initializer_vec_index _ _ segment found, bind_ok, passive] at success
  obtain ⟨⟨result, b1, indices⟩, pushed, rest⟩ := initializer_bind_success success
  have output := Result.ok_injective rest
  have sameResult := congrArg Prod.fst output
  dsimp only at sameResult
  subst result
  have fields := congrArg (fun out => out.2.1) output
  dsimp only at fields
  subst after
  obtain ⟨_, pushedValues⟩ := budget_push_success ops law budget b1 module.data_offsets indices none pushed
  exact ⟨rfl, pushedValues⟩

end Itasca.Runtime.Compiler

end

/-! ## InitializerMappingLoops -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Indexed source expressions and their retained synthetic functions. -/
def InitializerEntries (functions : List runtime.bytecode.CompiledFunction)
    (expressions : List Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (indices : List Usize) : Prop :=
  List.Forall₂ (fun expr index => InitializerAt functions index expr ty) expressions indices

theorem InitializerEntries.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {expressions ty indices}
    (entries : InitializerEntries before expressions ty indices) :
    InitializerEntries after expressions ty indices := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def GlobalInitializerEntries (functions : List runtime.bytecode.CompiledFunction)
    (globals : List Itasca.metadata.Global) (indices : List Usize) : Prop :=
  List.Forall₂ (fun global index => InitializerAt functions index global.init global.gtype.valtype)
    globals indices

theorem GlobalInitializerEntries.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {globals indices}
    (entries : GlobalInitializerEntries before globals indices) :
    GlobalInitializerEntries after globals indices := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def GlobalMappingPrefix (before current : runtime.compiler.ExecutableModule) (count : Nat) : Prop :=
  current = { before with functions := current.functions, global_initializers := current.global_initializers } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  GlobalInitializerEntries current.functions.val (before.module.env.globals.val.take count)
    current.global_initializers.val

theorem global_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : GlobalMappingPrefix before current index.val)
    (bound : index.val < before.module.env.globals.val.length)
    (success : runtime.compiler.initialize.lower_global ops current budget index =
      .ok (.Ok (), after, budgetAfter)) : GlobalMappingPrefix before after (index.val + 1) := by
  obtain ⟨unchanged, prefixEq, entries⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let global := before.module.env.globals.val[index.val]
  have found : current.module.env.globals.val[index.val]? = some global := by
    rw [source]
    exact List.getElem?_eq_getElem bound
  obtain ⟨function, fnIndex, cert, position, changed, functions, indices⟩ :=
    initializer_lower_global ops law current after budget budgetAfter index global found success
  have extended := entries.extend (after := after.functions.val) (by simp [functions])
  refine ⟨?_, ?_, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · rw [functions, List.take_append_of_le_length]
    · exact prefixEq
    · have hlen := congrArg List.length prefixEq
      simp only [List.length_take] at hlen
      change before.functions.val.length ≤ current.functions.val.length
      omega
  · unfold GlobalInitializerEntries at extended ⊢
    rw [List.take_add_one, indices]
    have single : List.Forall₂
        (fun global index => InitializerAt after.functions.val index global.init global.gtype.valtype)
        [global] [fnIndex] := by
      refine .cons ?_ .nil
      refine ⟨function, ?_, cert⟩
      rw [functions, position]
      simp
    simpa [List.getElem?_eq_getElem bound, global] using List.rel_append extended single

/-- Successful completion of the actual global initializer loop retains a
certificate for each source global, with exact module-field preservation. -/
theorem initializer_global_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : GlobalMappingPrefix before current index.val)
    (bound : index.val ≤ before.module.env.globals.val.length)
    (success : runtime.compiler.initialize.lower_loop0 ops current budget index (.Ok ()) =
      .ok (after, budgetAfter, .Ok ())) :
    GlobalMappingPrefix before after before.module.env.globals.val.length := by
  classical
  let measure := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    if p.2.2.2 = .Ok () then before.module.env.globals.val.length - p.2.2.1.val + 1 else 0
  let inv := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2 = .Ok () → p.2.2.1.val ≤ before.module.env.globals.val.length ∧
      GlobalMappingPrefix before p.1 p.2.2.1.val
  let post := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2 = .Ok () → GlobalMappingPrefix before p.1 before.module.env.globals.val.length
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop0.body ops state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨module, b, i, status⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop0.body at body
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok] at body
    cases status with
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at body
      split at body <;> (have hf := Result.ok_injective body; subst flow; simp [post])
    | Ok unit =>
      cases unit
      obtain ⟨hi, prefixInv⟩ := hinv rfl
      have source := congrArg runtime.compiler.ExecutableModule.module prefixInv.1
      dsimp only at source
      rw [source] at body
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : i.val < before.module.env.globals.val.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextModule, nextBudget⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := before.module.env.globals.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added] at addSpec
        simp only [WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unit =>
          cases unit
          have nextPrefix := global_mapping_append ops law before module nextModule b nextBudget i prefixInv hmore lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, by simpa [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = before.module.env.globals.val.length := by
          simp [alloc.vec.Vec.deref] at stopped
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        simpa [stop] using prefixInv
  have result := initializer_loop_success
    (fun p => runtime.compiler.initialize.lower_loop0.body ops p.1 p.2.1 p.2.2.1 p.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (current, budget, index, .Ok ()) (by exact fun _ => ⟨bound, prefixInv⟩)
    (after, budgetAfter, .Ok ()) success
  exact result rfl

end Itasca.Runtime.Compiler

end

/-! ## InitializerElementAppend -/

section

/-!
Element initializer mappings and append composition. ElementMappingPrefix and OffsetInitializer transport emitted element values and their source offset.
-/

/-! ## Initializer Element Mappings -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def ElementMappingPrefix (before current : runtime.compiler.ExecutableModule)
    (segment : Itasca.metadata.Element) (count : Nat) (indices : alloc.vec.Vec Usize) : Prop :=
  current = { before with functions := current.functions } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  InitializerEntries current.functions.val (segment.init.val.take count)
    (Itasca.ModuleConstants.referenceValueType segment.elem) indices.val

theorem element_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (prefixInv : ElementMappingPrefix before current segment j.val indices)
    (bound : j.val < segment.init.val.length)
    (success : runtime.compiler.initialize.lower_element_value ops current budget indices i j =
      .ok (.Ok (), after, budgetAfter, outIndices)) :
    ElementMappingPrefix before after segment (j.val + 1) outIndices := by
  obtain ⟨unchanged, prefixEq, entries⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let expr := segment.init.val[j.val]
  have exprFound : segment.init.val[j.val]? = some expr := List.getElem?_eq_getElem bound
  obtain ⟨function, fnIndex, cert, position, changed, functions, indices⟩ :=
    initializer_lower_element_value ops law current after budget budgetAfter indices outIndices i j
      segment expr (by simpa [source] using found) exprFound success
  have extended := entries.extend (after := after.functions.val) (by simp [functions])
  refine ⟨?_, ?_, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · rw [functions, List.take_append_of_le_length]
    · exact prefixEq
    · have hlen := congrArg List.length prefixEq
      simp only [List.length_take] at hlen
      change before.functions.val.length ≤ current.functions.val.length
      omega
  · unfold InitializerEntries at extended ⊢
    rw [List.take_add_one, indices]
    have single : List.Forall₂
        (fun expr index => InitializerAt after.functions.val index expr
          (Itasca.ModuleConstants.referenceValueType segment.elem)) [expr] [fnIndex] := by
      refine .cons ?_ .nil
      refine ⟨function, ?_, cert⟩
      rw [functions, position]
      simp
    simpa [List.getElem?_eq_getElem bound, expr] using List.rel_append extended single

/-- Successful evaluation of the actual inner compiler loop establishes the
complete vector of element-value initializer certificates. -/
theorem initializer_element_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (prefixInv : ElementMappingPrefix before current segment j.val indices)
    (bound : j.val ≤ segment.init.val.length)
    (success : runtime.compiler.initialize.lower_element_loop ops current budget i indices j (.Ok ()) =
      .ok (after, budgetAfter, outIndices, .Ok ())) :
    ElementMappingPrefix before after segment segment.init.val.length outIndices := by
  classical
  let measure := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      alloc.vec.Vec Usize × Usize × core.result.Result Unit Itasca.error.VisitError =>
    if p.2.2.2.2 = .Ok () then segment.init.val.length - p.2.2.2.1.val + 1 else 0
  let inv := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      alloc.vec.Vec Usize × Usize × core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2.2 = .Ok () → p.2.2.2.1.val ≤ segment.init.val.length ∧
      ElementMappingPrefix before p.1 segment p.2.2.2.1.val p.2.2.1
  let post := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      alloc.vec.Vec Usize × core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2 = .Ok () → ElementMappingPrefix before p.1 segment segment.init.val.length p.2.2.1
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_element_loop.body ops i state.1 state.2.1
        state.2.2.1 state.2.2.2.1 state.2.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨module, b, values, k, status⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_element_loop.body at body
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok] at body
    cases status with
    | Err error =>
      obtain ⟨actualSegment, indexed, rest⟩ := initializer_bind_success body
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at rest
      split at rest <;> (have hf := Result.ok_injective rest; subst flow; simp [post])
    | Ok unit =>
      cases unit
      obtain ⟨hk, prefixInv⟩ := hinv rfl
      have source := congrArg runtime.compiler.ExecutableModule.module prefixInv.1
      dsimp only at source
      rw [source, initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok] at body
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : k.val < segment.init.val.length := by simpa using more
        obtain ⟨⟨result, nextModule, nextBudget, nextValues⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : k + 1#usize ⦃ next => next.val = k.val + 1 ⦄ := by
          have size := segment.init.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added] at addSpec
        simp only [WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unit =>
          cases unit
          have nextPrefix := element_mapping_append ops law before module nextModule b nextBudget
            values nextValues i k segment found prefixInv hmore lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, by simpa [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : k.val = segment.init.val.length := by simp at stopped; omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        simpa [stop] using prefixInv
  have result := initializer_loop_success
    (fun p => runtime.compiler.initialize.lower_element_loop.body ops i p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow)
    (current, budget, indices, j, .Ok ()) (by exact fun _ => ⟨bound, prefixInv⟩)
    (after, budgetAfter, outIndices, .Ok ()) success
  exact result rfl

end Itasca.Runtime.Compiler

end

/-! ## Initializer Element Append -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def sourceElementOffset (segment : Itasca.metadata.Element) : Option Itasca.wasm_types.ConstExpr :=
  match segment.mode with
  | .Active _ expr => some expr
  | .Passive | .Declarative => none

def OffsetInitializer (functions : List runtime.bytecode.CompiledFunction)
    (expr : Option Itasca.wasm_types.ConstExpr) (index : Option Usize) : Prop :=
  match expr, index with
  | none, none => True
  | some expr, some index => InitializerAt functions index expr .I32
  | _, _ => False

theorem OffsetInitializer.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {expr index}
    (cert : OffsetInitializer before expr index) : OffsetInitializer after expr index := by
  cases expr <;> cases index <;> simp only [OffsetInitializer] at cert ⊢
  exact cert.extend prefixEq

theorem element_offset_found (env : Itasca.metadata.Env) (index : Usize)
    (segment : Itasca.metadata.Element) (found : env.elements.val[index.val]? = some segment) :
    runtime.compiler.initialize.element_offset env index = .ok (sourceElementOffset segment) := by
  unfold runtime.compiler.initialize.element_offset
  simp only [Itasca.metadata.Env.impl.elements, bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok]
  unfold sourceElementOffset
  cases segment.mode <;> rfl

theorem initializer_lower_element {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Element)
    (found : module.module.env.elements.val[index.val]? = some segment)
    (success : runtime.compiler.initialize.lower_element ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ indices offset,
      after = { module with functions := after.functions, element_initializers := after.element_initializers, element_offsets := after.element_offsets } ∧
      after.functions.val.take module.functions.length = module.functions.val ∧
      after.element_initializers.val = module.element_initializers.val ++ [indices] ∧
      after.element_offsets.val = module.element_offsets.val ++ [offset] ∧
      InitializerEntries after.functions.val segment.init.val
        (Itasca.ModuleConstants.referenceValueType segment.elem) indices.val ∧
      OffsetInitializer after.functions.val (sourceElementOffset segment) offset := by
  unfold runtime.compiler.initialize.lower_element at success
  obtain ⟨⟨middle, b1, indices, result⟩, loopCall, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    have initial : ElementMappingPrefix module module segment 0 (alloc.vec.Vec.new Usize) := by
      refine ⟨rfl, by simp, ?_⟩
      exact .nil
    obtain ⟨changed, prefixEq, entries⟩ := initializer_element_loop ops law module module middle budget b1
      (alloc.vec.Vec.new Usize) indices index 0#usize segment found initial (by simp) loopCall
    simp only [List.take_length] at entries
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨result, b2, rows⟩, pushed, rest⟩ := initializer_bind_success rest
    cases result with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      obtain ⟨_, rowsEq⟩ := budget_push_success ops law b1 b2 middle.element_initializers rows indices pushed
      have source := congrArg runtime.compiler.ExecutableModule.module changed
      have oldRows := congrArg runtime.compiler.ExecutableModule.element_initializers changed
      have oldOffsets := congrArg runtime.compiler.ExecutableModule.element_offsets changed
      dsimp only at source oldRows oldOffsets
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env,
        uncurry_apply_pair, source] at rest
      rw [element_offset_found _ _ segment found, bind_ok] at rest
      cases offsetEq : sourceElementOffset segment with
      | none =>
        rw [offsetEq] at rest
        obtain ⟨⟨result, b3, offsets⟩, pushedOffset, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        have sameResult := congrArg Prod.fst output
        dsimp only at sameResult
        subst result
        have fields := congrArg (fun out => out.2.1) output
        dsimp only at fields
        subst after
        obtain ⟨_, offsetsEq⟩ := budget_push_success ops law b2 b3 middle.element_offsets offsets none pushedOffset
        refine ⟨indices, none, ?_, prefixEq, ?_, ?_, entries, ?_⟩
        · rw [changed]
        · simpa only [oldRows] using rowsEq
        · simpa only [oldOffsets] using offsetsEq
        · simp [OffsetInitializer, offsetEq]
      | some expr =>
        rw [offsetEq] at rest
        obtain ⟨⟨result, final, b3⟩, expression, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok fnIndex =>
          obtain ⟨function, certificate, position, finalEq, functions⟩ :=
            initializer_expression ops law { middle with element_initializers := rows } b2 expr .I32
              fnIndex final b3 (by simpa only [source] using expression)
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
          obtain ⟨⟨result, b4, offsets⟩, pushedOffset, rest⟩ := initializer_bind_success rest
          have output := Result.ok_injective rest
          have sameResult := congrArg Prod.fst output
          dsimp only at sameResult
          subst result
          have fields := congrArg (fun out => out.2.1) output
          dsimp only at fields
          subst after
          obtain ⟨_, offsetsEq⟩ := budget_push_success ops law b3 b4 final.element_offsets offsets (some fnIndex) pushedOffset
          have finalRows := congrArg runtime.compiler.ExecutableModule.element_initializers finalEq
          have finalOffsets := congrArg runtime.compiler.ExecutableModule.element_offsets finalEq
          dsimp only at finalRows finalOffsets functions position
          have extended := entries.extend (after := final.functions.val) (by simp [functions])
          refine ⟨indices, some fnIndex, ?_, ?_, ?_, ?_, extended, ?_⟩
          · rw [finalEq]
            conv_lhs => rw [changed]
          · rw [functions, List.take_append_of_le_length]
            · exact prefixEq
            · have hlen := congrArg List.length prefixEq
              simp only [List.length_take] at hlen
              change module.functions.val.length ≤ middle.functions.val.length
              omega
          · simpa only [finalRows, oldRows] using rowsEq
          · simpa only [finalOffsets, oldOffsets] using offsetsEq
          · simp only [OffsetInitializer, offsetEq]
            refine ⟨function, ?_, certificate⟩
            rw [functions, position]
            simp

end Itasca.Runtime.Compiler

end

end
