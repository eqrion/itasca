import Itasca.Runtime.Compiler.Local.Initializer.InitializerMappingLoops

/-!
Element initializer mappings and append composition. ElementMappingPrefix and OffsetInitializer transport emitted element values and their source offset.
-/

/-! ## Initializer Element Mappings -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def ElementMappingPrefix (before current : runtime.compiler.ExecutableModule)
    (segment : Itasca.module.Element) (count : Nat) (indices : alloc.vec.Vec Usize) : Prop :=
  current = { before with functions := current.functions } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  InitializerEntries current.functions.val (segment.init.val.take count)
    (Itasca.ModuleConstants.referenceValueType segment.elem) indices.val

theorem element_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.module.Element)
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
    (i j : Usize) (segment : Itasca.module.Element)
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
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok] at body
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

end Itasca.Runtime.Code

end

/-! ## Initializer Element Append -/

section

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

end
