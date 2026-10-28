import Exec.Code.Local.Initializer.InitializerElementMappings

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def sourceElementOffset (segment : Itasca.module.Element) : Option Itasca.types.ConstExpr :=
  match segment.mode with
  | .Active _ expr => some expr
  | .Passive | .Declarative => none

def OffsetInitializer (functions : List runtime.bytecode.CompiledFunction)
    (expr : Option Itasca.types.ConstExpr) (index : Option Usize) : Prop :=
  match expr, index with
  | none, none => True
  | some expr, some index => InitializerAt functions index expr .I32
  | _, _ => False

theorem OffsetInitializer.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {expr index}
    (cert : OffsetInitializer before expr index) : OffsetInitializer after expr index := by
  cases expr <;> cases index <;> simp only [OffsetInitializer] at cert ⊢
  exact cert.extend prefixEq

theorem element_offset_found (env : Itasca.module.Env) (index : Usize)
    (segment : Itasca.module.Element) (found : env.elements.val[index.val]? = some segment) :
    runtime.compiler.initialize.element_offset env index = .ok (sourceElementOffset segment) := by
  unfold runtime.compiler.initialize.element_offset
  simp only [Itasca.module.Env.impl.elements, bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok]
  unfold sourceElementOffset
  cases segment.mode <;> rfl

theorem initializer_lower_element {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.module.Element)
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
        runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env,
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

end Itasca.Runtime.Code
